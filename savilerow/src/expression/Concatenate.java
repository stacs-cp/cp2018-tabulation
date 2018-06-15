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
import savilerow.model.*;
import savilerow.treetransformer.*;

// Join a matrix of 1-dimensional matrices into one matrix. 

public class Concatenate extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public Concatenate(ArrayList<ASTNode> a) {
        super(a);
    }
    public Concatenate(ASTNode[] a) {
        super(a);
    }
    
    public ASTNode copy()
    {
        return new Concatenate(getChildrenArray());
    }
    
    public boolean typecheck(SymbolTable st) {
        for(int i=0; i<numChildren(); i++) {
            if(! getChild(i).typecheck(st)) return false;
            if(getChild(i).getDimension()<1) {
                System.out.println("ERROR: Expected 1-dimensional or greater matrix inside concatenate: "+this);
                return false;
            }
        }
        return true;
	}
    
    public ASTNode simplify()
    {
        // Check everything is a matrix literal
        for(int i=0; i<numChildren(); i++) {
            if( ! (getChild(i) instanceof CompoundMatrix || getChild(i) instanceof EmptyMatrix 
                || (getChild(i) instanceof Identifier && getChild(i).getCategory()==ASTNode.Constant))) {
                return null;
            }
        }
        
        ArrayList<ASTNode> cm=new ArrayList<ASTNode>();
        
        for(int i=0; i<numChildren(); i++) {
            ASTNode inner=getChildConst(i);
            if(getChild(i) == inner) {
                inner.detachChildren();
            }
            cm.addAll(inner.getChildren(1));
        }
        return CompoundMatrix.make(cm);
    }
    
    public int getDimension() {
        if(numChildren()==0) return 1;
        return getChild(0).getDimension();
    }
    
	public String toString()
	{
	    StringBuilder b=new StringBuilder();
	    b.append("flatten([");
	    for(int i=0; i<numChildren(); i++) {
	        b.append(getChild(i));
	        if(i<numChildren()-1) b.append(",");
	    }
	    b.append("],1)");
	    return b.toString();
	}
}
