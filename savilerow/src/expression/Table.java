package savilerow.expression;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2017 Peter Nightingale
    
    This file is part of Savile Row.
    
    Savile Row is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.
    
    Savile Row is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.
    
    You should have received a copy of the GNU General Public License
    along with Savile Row.  If not, see <http://www.gnu.org/licenses/>.

*/

import savilerow.*;
import savilerow.model.*;
import java.util.*;
import java.io.*;
import savilerow.model.Sat;

public class Table extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    protected transient Model m;
    
    public Table(Model _m, ASTNode v, ASTNode tups) {
        super(v,tups);
        m=_m;
    }
    
    public boolean hasModel() {
        return true;
    }
    public Model getModel() {
        return m;
    }
    public void setModel(Model _m) {
        m=_m;
    }
    
	public ASTNode copy()
	{
	    return new Table(m, getChild(0), getChild(1));
	}
	public boolean isRelation(){return true;}
	public boolean strongProp() {
        return getChild(0).strongProp();
    }
	public boolean typecheck(SymbolTable st) {
	    if(!getChild(0).typecheck(st)) return false;
	    if(!getChild(1).typecheck(st)) return false;
	    
	    if(getChild(0).getDimension()!=1) {
            CmdFlags.println("ERROR: First argument of table should be 1-dimensional matrix: "+this);
            return false;
        }
	    if(getChild(1).getDimension()!=2) {
	        CmdFlags.println("ERROR: Second argument of table should be 2-dimensional matrix: "+this);
            return false;
	    }
	    
        return true;
    }
    
    public ASTNode simplify() {
        ASTNode c0=getChildConst(0);
        if((c0 instanceof CompoundMatrix || c0 instanceof EmptyMatrix) && (getChild(1).getCategory()==ASTNode.Constant)) {
            ASTNode table=getChildConst(1);
            if(table==getChild(1) && (table instanceof CompoundMatrix || table instanceof EmptyMatrix)) {
                // Also of category constant, must be a matrix literal. 
                
                if(table instanceof EmptyMatrix) {
                    return new BooleanConstant(false);
                }
                
                // Make an identifier for it and store elsewhere.
                
                // Store table in deduplicated store.
                ASTNode tabid=m.cmstore.newConstantMatrixDedup(table);
                getChild(0).setParent(null);
                return new Table(m, getChild(0), tabid);
            }
            
            if(table instanceof CompoundMatrix || table instanceof EmptyMatrix) {
                // Both vars and table are matrix types we can work with. 
                
                if(table instanceof EmptyMatrix) {
                    // It's an empty vector of tuples, not a vector containing a single empty tuple. 
                    return new BooleanConstant(false);
                }
                
                if(c0 instanceof EmptyMatrix) {
                    // ... and table is non-empty
                    return new BooleanConstant(true);
                }
                
                if(c0.numChildren()==2) {
                    // Only one var in scope.  Convert the table to a set and the table constraint into an in.
                    if(c0==getChild(0)) {
                        c0.getChild(1).setParent(null);
                    }
                    return new InSet(c0.getChild(1), new ToSet(new Flatten(table)));
                }
                
                // Simple one -- just project out assigned variables. 
                boolean filt=false;
                for(int i=1; i<c0.numChildren(); i++) {
                    if(c0.getChild(i).isConstant()) {
                        filt=true;
                        break;
                    }
                }
                
                if(filt) {
                    ArrayList<ASTNode> vars=c0.getChildren(1);
                    ArrayList<ASTNode> newtab=table.getChildren(1);
                    
                    for(int i=vars.size()-1; i>=0; i--) {
                        if(vars.get(i).isConstant()) {
                            long val=vars.get(i).getValue();
                            vars.remove(i);
                            
                            // Filter the table.
                            ArrayList<ASTNode> newtab2=new ArrayList<ASTNode>();
                            for(int j=0; j<newtab.size(); j++) {
                                if(newtab.get(j).getChild(i+1).getValue() == val) {
                                    ArrayList<ASTNode> tmp=newtab.get(j).getChildren(1);
                                    tmp.remove(i);  // Get rid of the column i
                                    
                                    newtab2.add(CompoundMatrix.make(tmp));
                                }
                            }
                            newtab=newtab2;
                        }
                    }
                    
                    ASTNode replacement_table=CompoundMatrix.make(newtab);
                    
                    // Store in deduplicated table store. 
                    replacement_table=m.cmstore.newConstantMatrixDedup(replacement_table);
                    
                    if(c0 == getChild(0)) {
                        for(int i=0; i<vars.size(); i++) {
                            vars.get(i).setParent(null);
                        }
                    }
                    return new Table(m, CompoundMatrix.make(vars), replacement_table);
                }
                return null;
                
                // Even simpler -- only evaluate when all variables are assigned.
                /*ArrayList<ASTNode> vars=c0.getChildren(1);
                long[] vals=new long[vars.size()];
                for(int i=0; i<vars.size(); i++) {
                    if(! vars.get(i).isConstant()) {
                        return null;
                    }
                    else {
                        vals[i]=vars.get(i).getValue();
                    }
                }
                
                for(int i=1; i<table.numChildren(); i++) {
                    ASTNode tuple=table.getChild(i);
                    
                    boolean tupleSatisfied=true;
                    for(int j=1; j<tuple.numChildren(); j++) {
                        if(tuple.getChild(j).getValue() != vals[j-1]) {
                            tupleSatisfied=false;
                            break;
                        }
                    }
                    if(tupleSatisfied) {
                        return new BooleanConstant(true);
                    }
                }
                return new BooleanConstant(false);*/
            }
        }
        return null;
    }
    
    @Override
    public boolean isNegatable() {
        return true;
    }
    @Override
    public ASTNode negation() {
        return new NegativeTable(m, getChild(0), getChild(1));
    }
    
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException
	{
	    assert bool_context;
	    if(getChild(0).numChildren()<=3) {
	        b.append("table(");
	    }
	    else {
	        b.append("table(");
	    }
	    getChild(0).toMinion(b, false);
	    b.append(", ");
	    if(getChild(1) instanceof CompoundMatrix || getChild(1) instanceof EmptyMatrix) {
	        ArrayList<ASTNode> tups=getChild(1).getChildren();
	        b.append("{");
            for(int i=1; i<tups.size(); i++)
            {
                ArrayList<ASTNode> elements=tups.get(i).getChildren();
                b.append("<");
                for(int j=1; j<elements.size(); j++)
                {
                    elements.get(j).toMinion(b, false);
                    if(j<elements.size()-1) b.append(", ");
                }
                b.append(">");
                
                if(i<tups.size()-1) b.append(", ");
            }
            b.append("}");
	    }
	    else
	        getChild(1).toMinion(b, false);
	    b.append(")");
	}
	public void toDominionInner(StringBuilder b, boolean bool_context)
	{
	    b.append(CmdFlags.getCtName()+" ");
	    b.append("table(flatten(");
	    getChild(0).toDominion(b, false);
	    b.append("), ");
	    getChild(1).toDominion(b, false);
	    b.append(")");
	}
	public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
	    if(CmdFlags.getGecodetrans()) {
	        b.append("constraint gecode_table_int(");
	    }
	    else {
	        b.append("constraint table_int(");
	    }
	    getChild(0).toFlatzinc(b, false);
	    b.append(",[");
	    ASTNode cmat=getChildConst(1);
	    
	    for(int i=1; i<cmat.numChildren(); i++) {
            for(int j=1; j<cmat.getChild(i).numChildren(); j++) {
                cmat.getChild(i).getChild(j).toFlatzinc(b, false);
                b.append(",");
            }
        }
        
        b.append("]);");
	}
	public void toMinizinc(StringBuilder b, boolean bool_context) {
	    b.append("table(");
	    getChild(0).toMinizinc(b, false);
	    b.append(",");
	    if(getChild(1) instanceof CompoundMatrix || getChild(1) instanceof EmptyMatrix) {
	        // Print out very strange Minizinc 2d array format.
	        ConstantMatrixStore.printMzn2darray(b, getChild(1));
	    }
	    else {
	        getChild(1).toMinizinc(b, false);
	    }
	    b.append(")");
	}
	
	
	public void toSAT(Sat satModel) throws IOException {
	    //toSATHelper(satModel, 0, false);
	    toSATHelper2(satModel);
	}
	public void toSATWithAuxVar(Sat satModel, long auxVar) throws IOException {
	    toSATHelper(satModel, auxVar, true);
	}
	
	////////////////////////////////////////////////////////////////////////////
	//
	//   First encoding of Table. Each tuple is represented with a SAT variable
	//   that is true iff the tuple is assigned. Then we have a disjunction of 
	//   these new SAT variables. Allows reification. 
	
	public void toSATHelper(Sat satModel, long auxVar, boolean toSATWithAuxVar) throws IOException {
        ASTNode tab=getChildConst(1);
        
        ArrayList<Long> newSatVars = new ArrayList<Long>(tab.numChildren());
        
        for (int i=1; i < tab.numChildren(); i++) {
            ASTNode tuple = tab.getChild(i);
            
            // One sat variable for each tuple. 
            long auxSatVar = satModel.createAuxSATVariable();
            
            ArrayList<Long> iffclause=new ArrayList<Long>();
            
            for (int j =1; j < tuple.numChildren(); j++) {
                long value=tuple.getChild(j).getValue();
                long satLit=getChild(0).getChild(j).directEncode(satModel, value);
                
                satModel.addClause(-auxSatVar, satLit);
                iffclause.add(-satLit);
            }
            
            iffclause.add(auxSatVar);
            satModel.addClause(iffclause);
            
            newSatVars.add(auxSatVar);
        }
        
        if(toSATWithAuxVar) {
            // Ensure one of the tuples is assigned iff auxVar
            satModel.addClauseReified(newSatVars, auxVar);
        }
        else {
            // Always ensure one of the tuples is assigned.
            satModel.addClause(newSatVars);
        }
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //   Second encoding of Table.
    //   Same as Bacchus except for final clause. 
    
    public void toSATHelper2(Sat satModel) throws IOException {
        ASTNode tab=getChildConst(1);
        
        ArrayList<ASTNode> tups=tab.getChildren();
        
        ArrayList<ASTNode> vardoms=new ArrayList<ASTNode>();
        for(int i=1; i<getChild(0).numChildren(); i++) {
            ASTNode var=getChild(0).getChild(i);
            if(var instanceof Identifier) {
                vardoms.add(((Identifier)var).getDomain());
            }
            else if(var.isConstant()) {
                vardoms.add(new IntegerDomain(new Range(var,var)));
            }
            else if(var instanceof SATLiteral) {
                vardoms.add(new BooleanDomainFull());
            }
            else {
                assert false : "Unknown type contained in table constraint:"+var;
            }
        }
        
        ArrayList<Long> tupleSatVars = new ArrayList<Long>(tups.size());
        
        // Make a SAT variable for each tuple. 
        for(int i=1; i < tups.size(); i++) {
            // Filter out tuples that are not valid.
            boolean valid=true;
            for(int var=1; var<getChild(0).numChildren(); var++) {
                if(!vardoms.get(var-1).containsValue(tups.get(i).getChild(var).getValue())) {
                    valid=false;
                    break;
                }
            }
            
            if(!valid) {
                tups.set(i, tups.get(tups.size()-1));
                tups.remove(tups.size()-1);
                i--;
                continue;
            }
            
            //  Make a new sat variable for the tuple
            tupleSatVars.add(satModel.createAuxSATVariable());
        }
        
        for(int var=1; var<getChild(0).numChildren(); var++) {
            ASTNode varast=getChild(0).getChild(var);
            
            ArrayList<Long> vals=vardoms.get(var-1).getValueSet();
            ArrayList<Intpair> vals_intervalset=vardoms.get(var-1).getIntervalSet();
            
            // For each value in vals, construct a list of all tuples (sat vars representing tuples) containing that value. 
            
            ArrayList<ArrayList<Long>> clauses=new ArrayList<ArrayList<Long>>(vals.size());
            
            for(int i=0; i<vals.size(); i++) {
                clauses.add(new ArrayList<Long>());
            }
            
            for(int tup=1; tup<tups.size(); tup++) {
                long valintup=tups.get(tup).getChild(var).getValue();
                
                // Find the value in the domain
                int childidx=-1;   /// out of bounds
                int cumulativeindex=0;
                for(int j=0; j<vals_intervalset.size(); j++) {
                    Intpair p=vals_intervalset.get(j);
                    if( valintup>=p.lower && valintup<=p.upper) {
                        childidx=(int) (valintup-p.lower+cumulativeindex);
                        break;
                    }
                    cumulativeindex+=p.upper-p.lower+1;
                }
                
                if(childidx==-1) {
                    // Not in domain. Current tuple is invalid.
                    assert false : "Should be no invalid tuples";
                    satModel.addClause(-tupleSatVars.get(tup-1));
                }
                else {
                    // Add the SAT var for this tuple to one of the clauses.
                    assert vals.get(childidx)==valintup;
                    clauses.get(childidx).add(tupleSatVars.get(tup-1));
                }
            }
            
            //  Now post the clauses 
            for(int i=0; i<vals.size(); i++) {
                satModel.addClauseReified(clauses.get(i), varast.directEncode(satModel, vals.get(i)));
            }
        }
        
        satModel.addClause(tupleSatVars);   // One of the tuples must be assigned -- redundant but probably won't hurt.
    }
    
}
