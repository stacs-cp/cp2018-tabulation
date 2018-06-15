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

//  Contains the exclusion expression of a mining problem. 
//  Stores it as a singleton in a static member. 

public class MultiStageOnSolution extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    
    public static ArrayList<ASTNode> sollist;
    public static ASTNode incl=null;
    
	public MultiStageOnSolution(ASTNode a) {
	    super(a);
	}
	
	public ASTNode copy() {
	    return new MultiStageOnSolution(getChild(0));
	}
	
	public boolean toFlatten(boolean propagate) { return false; }
	public boolean isRelation() {
        return true;
    }
    
    @Override
    public boolean typecheck(SymbolTable st) {
        if(!getChild(0).typecheck(st)) {
            return false;
        }
        if( getChild(0).getDimension()>0 || !getChild(0).isRelation()) {
            CmdFlags.typeError("Expected constraint in multiStageOnSolution: "+this);
            return false;
        }
        return true;
    }
    
    public ASTNode simplify() {
        if(CmdFlags.getAfterAggregate()) {
            //  Delay this until after quantifier unrolling, matrix replacement.
            incl=getChild(0);
            return new BooleanConstant(true);
        }
        return null;
    }
    
	public String toString() {
	    return "multiStageOnSolution("+getChild(0)+")";
	}
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
        // Do nothing.
    }
}
