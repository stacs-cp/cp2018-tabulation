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


import java.util.*;
import savilerow.model.SymbolTable;

// Subset for sets/domains that are constant after parameter substitution.

public class Subset extends SetBinOp
{
    public static final long serialVersionUID = 1L;
	public Subset(ASTNode l, ASTNode r)
	{
		super(l, r);
	}
	
	public ASTNode copy()
	{
	    return new Subset(getChild(0), getChild(1));
	}
	public boolean isRelation(){return true;}
	
	public boolean toFlatten(boolean propagate) { return false;}
	
    public ASTNode simplify() {
        if(getChild(0).getCategory()==ASTNode.Constant && getChild(1).getCategory()==ASTNode.Constant) {
            ArrayList<Intpair> a=getChild(0).getIntervalSet();
            ArrayList<Intpair> b=getChild(1).getIntervalSet();
            
            ArrayList<Intpair> diff=Intpair.setDifference(a,b);
            
            return new BooleanConstant(diff.size()==0 && ! a.equals(b));
        }
        return null;
    }
    
	public String toString() {
	    return "("+getChild(0)+" subset "+getChild(1)+")";
	}
}
