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

// Element(matrix or matrix slice, index expression) is a function to the result.
// Indexes from 0. 

public class Element extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public Element(ASTNode arr, ASTNode ind) {
        super(arr, ind);
    }
    
	public ASTNode copy()
	{
	    return new Element(getChild(0), getChild(1));
	}
	
	public boolean isRelation(){
	    return getChild(0).isRelation();}
	@Override public boolean strongProp() {
	    return getChild(0).strongProp() && getChild(1).strongProp();
	}
	public boolean isNumerical() {
        return getChild(0).isNumerical();}
    
    public boolean toFlatten(boolean propagate) {
        if(this.isNumerical()) {
            return true;
        }
        return super.toFlatten(propagate);  // Hand over to ASTNode.toFlatten
    }
    
	// Why is this here? Element is not in the input language.
	public boolean typecheck(SymbolTable st) {
	    for(int i=0; i<2; i++) { if(!getChild(i).typecheck(st)) return false; }
        if(getChild(0).getDimension()!=1) {
            CmdFlags.println("ERROR: Expected one-dimensional matrix for first argument of element constraint: "+this);
            return false;
        }
        return true;
    }
    
    @Override public ASTNode simplify() {
        // if getChild(0) is an EmptyMatrix then index must be out of bounds -- so do nothing. 
        ASTNode mat=getChildConst(0);
        
        if(mat instanceof CompoundMatrix) {
            if(getChild(1).isConstant()) {     // If the index is a constant, evaluate it. 
                long idx=getChild(1).getValue();
                if(idx<0 || idx>=(mat.numChildren()-1)) {
                    return null;   // out of bounds -- do not attempt to evaluate it. 
                }
                else {
                    ASTNode elem=mat.getChild( (int)idx+1 );  // Index from 0. Index domain is in position 0.
                    if(mat==getChild(0)) {
                        elem.setParent(null);
                    }
                    return elem;
                }
            }
            
            Intpair a=getChild(1).getBounds();
            int numelements=mat.numChildren()-1;
            
            if(a.upper<numelements-1) {
                // Always safe to trim the right-hand end of the matrix
                ArrayList<ASTNode> newelements=new ArrayList<ASTNode>((int) (a.upper+1));
                if(mat==getChild(0)) {
                    mat.detachChildren();
                }
                getChild(1).setParent(null);
                for(int i=1; i<=a.upper+1; i++) {
                    newelements.add(mat.getChild(i));
                }
                return new Element(CompoundMatrix.make(newelements), getChild(1));
            }
            
            //  IF the index is not yet flattened, then trim both ends.
            if(getChild(1).toFlatten(false) && (a.lower>0 || a.upper<numelements-1)) {
                // Trim the ends of the compound matrix by the bounds of the index variable. 
                // Does not deal with holes in the index domain. This would require a table constraint.     
                // Potentially unflattens the index variable. dangerous. 
                ArrayList<ASTNode> newelements=new ArrayList<ASTNode>((int) (a.upper-a.lower+1));
                
                if(a.lower<0) a.lower=0;
                if(a.upper>numelements-1) a.upper=numelements-1;
                if(mat==getChild(0)) {
                    mat.detachChildren();
                }
                getChild(1).setParent(null);
                for(int i=(int)a.lower; i<=a.upper; i++) newelements.add(mat.getChild(i+1));
                return new Element(CompoundMatrix.make(newelements), BinOp.makeBinOp("-", getChild(1), NumberConstant.make(a.lower)));
            }
	    }
	    
	    return null;
	}
	
	public Intpair getBounds() {
	    Intpair a=getChild(0).getBounds();
	    return lookupBounds(a);    //  Look up in FilteredDomainStore
	}
	public PairASTNode getBoundsAST() {
	    return getChild(0).getBoundsAST();
	}
	
	public ArrayList<Intpair> getIntervalSetExp() {
	    ArrayList<Intpair> a=getChild(0).getChild(1).getIntervalSetExp();
	    for(int i=2; i<getChild(0).numChildren(); i++) {
	        a=Intpair.union(a, getChild(0).getChild(i).getIntervalSetExp());
	    }
	    return a;
    }
    
	@Override
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
	    assert bool_context;
	    assert this.isRelation();
	    this.toMinionWithAuxVar(b, new BooleanConstant(true));
	}
	
	public void toMinionWithAuxVar(BufferedWriter b, ASTNode aux) throws IOException
	{
	    // Might need to use an element rather than watchelement.
	    if(CmdFlags.getUseBoundVars() && 
	        (aux.exceedsBoundThreshold() || getChild(0).exceedsBoundThreshold() || getChild(1).exceedsBoundThreshold() )) {
	        b.append("element(");
	    }
	    else {
	        b.append("watchelement(");
	    }
	    
	    getChild(0).toMinion(b, false);
	    b.append(", ");
	    getChild(1).toMinion(b, false);
	    b.append(", ");
	    aux.toMinion(b, false);
	    b.append(")");
	}
	public void toDominionWithAuxVar(StringBuilder b, ASTNode aux)
	{
	    b.append(CmdFlags.getCtName()+" ");
	    b.append("element(flatten(");
	    getChild(0).toDominion(b, false);
	    b.append("), ");
	    getChild(1).toDominion(b, false);
	    b.append(", ");
	    aux.toDominion(b, false);
	    b.append(")");
	}
}
