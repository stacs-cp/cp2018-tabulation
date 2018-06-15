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

import savilerow.model.*;
import java.io.*;

// The top of the AST for constraints. Usually contains an And. 

public class Top extends ASTNodeC {
    public static final long serialVersionUID = 1L;
    public Top(ASTNode in) {
        super(in);
    }
    
	public ASTNode copy() {
	    return new Top(getChild(0));
	}
	
	public String toString() { return getChild(0).toString(); }
	public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException { 
	    getChild(0).toFlatzinc(b, true);
	    b.append("\n");
	}
	public void toMinizinc(StringBuilder b, boolean context) {
	    if(getChild(0) instanceof And) {
	        getChild(0).toMinizinc(b, context);
	    }
	    else {
	        b.append("constraint ");
	        getChild(0).toMinizinc(b, context);
	        b.append(";\n");
	    }
	}
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
	    assert bool_context;
	    getChild(0).toMinion(b, true);
	}
	public void toSAT(Sat satModel) throws IOException {
	    if(getChild(0) instanceof BooleanConstant) {
	        if(getChild(0).getValue()==1) {
	            // output nothing  --  formula is trivially satisfiable.
	        }
	        else {
	            // make an unsatisfiable formula by using the true var.
	            satModel.addClause(-satModel.getTrue());
	        }
	    }
	    else {
	        if(! (getChild(0) instanceof And)) {
	            satModel.addComment(String.valueOf(getChild(0)).replaceAll("\n", " "));
	        }
	        getChild(0).toSAT(satModel);
	    }
	}
	public void toDominionInner(StringBuilder b, boolean bool_context) { getChild(0).toDominion(b, bool_context); }
	
	public boolean inTopConjunction() { return true; }
	public boolean inTopAnd() { return true; }
	
	public boolean isRelation() { return false; }
}
