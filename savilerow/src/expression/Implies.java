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
import java.util.*;
import java.io.*;
import savilerow.model.SymbolTable;
import savilerow.model.Sat;

//  Logical implication.
//  When targeting Minion, also appears in output as reifyimply. 

public class Implies extends LogicBinOp
{
    public static final long serialVersionUID = 1L;
	public Implies(ASTNode l, ASTNode r)
	{
		super(l, r);
	}
	
	public ASTNode copy()
	{
	    return new Implies(getChild(0), getChild(1));
	}
	public boolean isRelation(){return true;}
	public boolean strongProp() {
	    return getChild(0).strongProp() && getChild(1).strongProp();
	}
	
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException
	{
	    assert bool_context;
	    if(getChild(1) instanceof Identifier || ( getChild(1) instanceof Negate && getChild(1).getChild(0) instanceof Identifier )) { 
            b.append("ineq(");
            getChild(0).toMinion(b, false);
            b.append(", ");
            getChild(1).toMinion(b, false);
            b.append(", 0)");
	    }
	    else {
	        // reify imply
	        b.append("reifyimply(");
	        getChild(1).toMinion(b, true);
	        b.append(", ");
	        getChild(0).toMinion(b, false);
	        b.append(")");
	    }
	}
	public void toDominionInner(StringBuilder b, boolean bool_context)
	{
	    b.append(CmdFlags.getCtName()+" ");
	    b.append("leq(");
	    getChild(0).toDominion(b, false);
	    b.append(", ");
	    getChild(1).toDominion(b, false);
	    b.append(")");
	}
	public void toDominionParam(StringBuilder b) {
	    b.append("Implies(");
	    getChild(0).toDominionParam(b);
	    b.append(",");
	    getChild(1).toDominionParam(b);
	    b.append(")");
	}
	public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
	    
	    b.append("constraint bool_clause([");
	    boolean second=false;
	    // Positive literals
	    if(getChild(0) instanceof Negate) {
	        getChild(0).getChild(0).toFlatzinc(b, true);  // Strip off the negation.
	        second=true;
	    }
	    if(! (getChild(1) instanceof Negate)) {
	        if(second) b.append(",");
	        getChild(1).toFlatzinc(b, true);
	    }
	    b.append("],[");
	    // Negative literals
	    second=false;
	    if(! (getChild(0) instanceof Negate)) {
	        getChild(0).toFlatzinc(b, true);
	        second=true;
	    }
	    if(getChild(1) instanceof Negate) {
	        if(second) b.append(",");
	        getChild(1).getChild(0).toFlatzinc(b, true);  // Strip off the negation.
	    }
	    b.append("]);");
	}
	public void toMinizinc(StringBuilder b, boolean bool_context) {
	    b.append("(");
	    getChild(0).toMinizinc(b, true);
	    b.append("->");
	    getChild(1).toMinizinc(b, true);
	    b.append(")");
	}
	public void toSAT(Sat satModel) throws IOException {
	    satModel.addClause(getChild(0).directEncode(satModel,0), getChild(1).directEncode(satModel,1) );
	}
	@Override
	public void toSATWithAuxVar(Sat satModel, long aux) throws IOException {
	    ArrayList<Long> c=new ArrayList<Long>();
	    c.add(getChild(0).directEncode(satModel,0));
	    c.add(getChild(1).directEncode(satModel,1));
	    satModel.addClauseReified(c, aux);
	}
	public ASTNode simplify() {
	    //  Basic rewrites -- one child is a constant
        if(getChild(0).isConstant() && getChild(0).getValue()==1) {
            getChild(1).setParent(null);
            return getChild(1);
        }
        if(getChild(0).isConstant() && getChild(0).getValue()==0) {
            return new BooleanConstant(true);
        }
        if(getChild(1).isConstant() && getChild(1).getValue()==1) {
            return new BooleanConstant(true);
        }
        if(getChild(1).isConstant() && getChild(1).getValue()==0) {
            getChild(0).setParent(null);
            return new Negate(getChild(0));
        }
        
        // Two children are symbolically equal
        if(getChild(0).equals(getChild(1))) return new BooleanConstant(true);
        
        if(getChild(0) instanceof And || getChild(1) instanceof Or) {   // Could also have getChild(1) is Implies, getParent is Or.
            //  In both of these cases the implication can merge into an existing disjunction.
            detachChildren();
            return new Or(new Negate(getChild(0)), getChild(1));
        }
        
        // Right side is a conjunction -- lift it through the implication.
        if(getChild(1) instanceof And) {
            ASTNode[] tmp=new ASTNode[getChild(1).numChildren()];
            for(int i=0; i<getChild(1).numChildren(); i++) {
                getChild(1).getChild(i).setParent(null);
                tmp[i]=new Implies(getChild(0), getChild(1).getChild(i));
            }
            return new And(tmp);
        }
        
        return null;
	}
	
	//  If contained in a Negate, push the negation inside using De Morgens law. 
	@Override
	public boolean isNegatable() {
	    return true;
	}
	@Override
	public ASTNode negation() {
	    return new And(getChild(0), new Negate(getChild(1)));
	}
	
	@Override
	public boolean typecheck(SymbolTable st) {
	    for(ASTNode child :  getChildren()) {
	        if(!child.typecheck(st))
	            return false;
	        if(!child.isRelation()) {
	            System.out.println("ERROR: Implication contains non-relation expression:"+child);
	            return false;
	        }
	    }
	    return true;
	}
	
	public String toString() {
	    return "("+getChild(0)+" -> "+getChild(1)+")";
	}
	
}