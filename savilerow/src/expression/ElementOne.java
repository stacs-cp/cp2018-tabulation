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

// ElementOne(matrix or matrix slice, index expression) is a function to the result.
//  One-based indexing for Gecode fz output.

public class ElementOne extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public ElementOne(ASTNode arr, ASTNode ind) {
        super(arr, ind);
    }
    
	public ASTNode copy()
	{
	    return new ElementOne(getChild(0), getChild(1));
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
    
	public ASTNode simplify() {
	    // if getChild(0) is an EmptyMatrix then index must be out of bounds -- so do nothing. 
        ASTNode mat=getChildConst(0);
        
        if(mat instanceof CompoundMatrix) {
            if(getChild(1).isConstant()) {     // If the index is a constant, evaluate it. 
                long idx=getChild(1).getValue();
                if(idx<1 || idx>=(mat.numChildren())) {
                    return null;   // out of bounds -- do not attempt to evaluate it. 
                }
                else {
                    ASTNode elem=mat.getChild( (int)idx );  // Index from 1. Index domain is in position 0.
                    if(mat==getChild(0)) {
                        elem.setParent(null);
                    }
                    return elem;
                }
            }
            
            Intpair a=getChild(1).getBounds();
            int numelements=mat.numChildren()-1;
            
            if(a.upper<numelements) {
                // Always safe to trim the right-hand end of the matrix
                ArrayList<ASTNode> newelements=list();
                if(mat==getChild(0)) {
                    mat.detachChildren();
                }
                getChild(1).setParent(null);
                for(int i=1; i<=a.upper; i++) newelements.add(mat.getChild(i));
                return new ElementOne(CompoundMatrix.make(newelements), getChild(1));
            }
            
            //  IF the index is not yet flattened, then trim both ends.
            if(getChild(1).toFlatten(false) && (a.lower>1 || a.upper<numelements)) {
                // Trim the ends of the compound matrix by the bounds of the index variable. 
                // Does not deal with holes in the index domain. This would require a table constraint.     
                // Potentially unflattens the index variable. dangerous. 
                ArrayList<ASTNode> newelements=list();
                
                if(a.lower<1) a.lower=1;
                if(a.upper>numelements) a.upper=numelements;
                if(mat==getChild(0)) {
                    mat.detachChildren();
                }
                getChild(1).setParent(null);
                for(long i=a.lower; i<=a.upper; i++) newelements.add(mat.getChild((int)i));
                return new ElementOne(CompoundMatrix.make(newelements), BinOp.makeBinOp("-", getChild(1), NumberConstant.make(a.lower-1)));
            }
	    }
	    
	    return null;
	}
	
	public Intpair getBounds() {
	    Intpair a = getChild(0).getBounds();
	    return lookupBounds(a);    //  Look up in FilteredDomainStore
	}
	
	public PairASTNode getBoundsAST() {
	    return getChild(0).getBoundsAST();
	}
	
	@Override
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
	    assert bool_context;
	    assert this.isRelation();
	    this.toMinionWithAuxVar(b, new BooleanConstant(true));
	}
	
	// Should not be using ElementOne when target is Minion -- however, when
	// target is something else we still need Minion output to do domain filtering. 
	public void toMinionWithAuxVar(BufferedWriter b, ASTNode aux) throws IOException
	{
	    // Make an Element. Child 0 must be a compound matrix/empty matrix
	    
	    ArrayList<ASTNode> tmp=getChild(0).getChildren();
	    tmp.set(0, NumberConstant.make(0));  // 0th element is a 0. 
	    
	    ASTNode e=new Element(CompoundMatrix.make(tmp), getChild(1));
	    
	    e.toMinionWithAuxVar(b, aux);
	}
	
	public void toFlatzincWithAuxVar(BufferedWriter b, ASTNode aux) throws IOException
	{
	    b.append("constraint array_var_int_element(");   // Could case split here for constant arrays using array_int_element -- Also there may be a bool version.
	    getChild(1).toFlatzinc(b, false);
	    b.append(", ");
	    getChild(0).toFlatzinc(b, false);
	    b.append(", ");
	    aux.toFlatzinc(b, false);
	    b.append(");");
	}
	
	public void toMinizinc(StringBuilder b,  boolean bool_context) {
	    b.append("(");
	    getChild(0).toMinizinc(b, bool_context);
	    b.append("[");
	    getChild(1).toMinizinc(b, bool_context);
	    b.append("])");
	}
}
