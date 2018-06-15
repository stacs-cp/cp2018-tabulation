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

//  Contains the sum from the cardinality constraint in a frequent item-set mining problem.

public class MultiStage extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
	public MultiStage(ASTNode a, ASTNode b)
	{
		super(a, b);
		CmdFlags.mining=true;
	}
	
	public ASTNode copy() {
	    return new MultiStage(getChild(0), getChild(1));
	}
	
	public boolean toFlatten(boolean propagate) { return false; }
	public boolean isRelation() {
        return true;
    }
    
    @Override
    public boolean typecheck(SymbolTable st) {
        if((!getChild(0).typecheck(st)) || (!getChild(1).typecheck(st))) {
	        return false;
	    }
	    
	    if(getChild(1).getDimension()!=1) {
	        CmdFlags.typeError("Expected list in multiStage constraint.");
	        return false;
	    }
	    if( !(getChild(0).isNumerical()) || getChild(0).getDimension()>0 ) {
	        CmdFlags.typeError("Expected numerical expression in multiStage constraint.");
	        return false;
	    }
        
        return true;
    }
    
	public ASTNode simplify()	{
	    return null;
	}
	
	public String toString() {
	    return "multiStage("+getChild(0)+","+getChild(1)+")";
	}
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
	    // no output to Minion.
    }
    public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
	    // no output to Fzn.
    }
}
