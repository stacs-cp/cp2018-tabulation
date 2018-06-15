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
// This one has default value 0 for out of range. Indexed from 0.

public class SafeElement extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public SafeElement(ASTNode arr, ASTNode ind)
    {
        super(arr, ind);
        assert !ind.isSet();
    }
    
	public ASTNode copy()
	{
	    return new SafeElement(getChild(0), getChild(1));
	}
	
	public boolean isRelation() {
	    return getChild(0).isRelation();
	}
	@Override public boolean strongProp() {
	    return getChild(0).strongProp() && getChild(1).strongProp();
	}
	public boolean isNumerical() {
        return getChild(0).isNumerical();
    }
    
    public boolean toFlatten(boolean propagate) {
        if(this.isNumerical()) {
            return true;
        }
        return super.toFlatten(propagate);  // Hand over to ASTNode.toFlatten
    }
    
    @Override public ASTNode simplify() {
        ASTNode mat=getChildConst(0);
        
        if(mat instanceof CompoundMatrix || mat instanceof EmptyMatrix) {
            if(getChild(1).isConstant()) {     // If the index is a constant, evaluate it. 
                long idx=getChild(1).getValue();
                if(idx<0 || idx>=(getChild(0).numChildren()-1)) {
                    return NumberConstant.make(0);   // default value.    Why only numerical????
                }
                else {
                    ASTNode elem=mat.getChild( (int)idx+1 );  // Index from 0. Index domain is in position 0.
                    if(mat==getChild(0)) {
                        elem.setParent(null);
                    }
                    return elem;
                }
            }
            
            if(mat.numChildren()==2) {
                // When SafeElement is introduced, the second child is 
                // bounded to be within the indices of the first child. So no need to
                // make sure second child =0.
                if(mat==getChild(0)) {
                    mat.getChild(1).setParent(null);
                }
                return mat.getChild(1);
            }
        }
        
        if(mat instanceof CompoundMatrix) {
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
                return new SafeElement(CompoundMatrix.make(newelements), getChild(1));
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
                return new SafeElement(CompoundMatrix.make(newelements), BinOp.makeBinOp("-", getChild(1), NumberConstant.make(a.lower)));
            }
	    }
	    
        //  Calculate if undef cannot occur. 
        if(getChild(0) instanceof CompoundMatrix || getChild(0) instanceof EmptyMatrix) {
            int numelements=getChild(0).numChildren()-1;
            Intpair b=getChild(1).getBounds();
            
            if(b.lower>=0 && b.upper<numelements) {
                detachChildren();
                return new Element(getChild(0), getChild(1));
            }
        }
        
	    return null;
	}
	
	public Intpair getBounds() {
	    Intpair a = getChild(0).getBounds();
	    if(a.lower>0) a.lower=0;    //  Add default value into range.
	    if(a.upper<0) a.upper=0;
	    return lookupBounds(a);    //  Look up in FilteredDomainStore
	}
	public PairASTNode getBoundsAST() {
	    PairASTNode a= getChild(0).getBoundsAST();
	    a.e1=new Min(a.e1, NumberConstant.make(0));   /// Add 0 into range, either below or above. 
	    a.e2=new Max(a.e2, NumberConstant.make(0));
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
	    // Might need to use an element rather than watchelement_undefzero.
	    if(CmdFlags.getUseBoundVars() && 
	        (aux.exceedsBoundThreshold() || getChild(0).exceedsBoundThreshold() || getChild(1).exceedsBoundThreshold() )) {
	        b.append("element_undefzero(");
	    }
	    else {
	        b.append("watchelement_undefzero(");
	    }
	    
	    getChild(0).toMinion(b, false);
	    b.append(", ");
	    getChild(1).toMinion(b, false);
	    b.append(", ");
	    aux.toMinion(b, false);
	    b.append(")");
	}
	
	// WARNING -- the Dominion output method drops the 'safety'
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
