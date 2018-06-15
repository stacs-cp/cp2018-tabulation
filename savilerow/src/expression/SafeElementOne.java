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

// Element(matrix or matrix slice, index expression) is a function to the result.
// This one has default value 0 for out of range. Indexed from 1.

public class SafeElementOne extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public SafeElementOne(ASTNode arr, ASTNode ind)
    {
        super(arr, ind);
    }
    
	public ASTNode copy()
	{
	    return new SafeElementOne(getChild(0), getChild(1));
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
	    // Turn into an ElementOne.
	    ASTNode mat=getChildConst(0);
	    if(mat instanceof CompoundMatrix || mat instanceof EmptyMatrix) {
	        // Turn it into ElementOne for output to Gecode/Chuffed/Minizinc
	        Intpair idxbnds=getChild(1).getBounds();
	        if(idxbnds.lower>=1 && idxbnds.upper<=mat.numChildren()-1) {
	            return new ElementOne(getChild(0), getChild(1));
            }
            else {
                // Make a new Mapping. 
                HashMap<Long, Long> map=new HashMap<Long, Long>();
                for(long domval=1; domval<=mat.numChildren()-1; domval++) {
                    map.put(domval, domval);
                }
                getChild(1).setParent(null);
                ASTNode mapping=new Mapping(map, getChild(1));
                // Default value of mapping will be mat.numChildren()  so add one more
                // element to child 0. 
                ArrayList<ASTNode> ch=mat.getChildren(1);
                if(mat == getChild(0)) {
                    for(int i=0; i<ch.size(); i++) {
                        ch.get(i).setParent(null);
                    }
                }
                ch.add(NumberConstant.make(0));  // Default value of the element.
                return new ElementOne(CompoundMatrix.make(ch), mapping);
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
}
