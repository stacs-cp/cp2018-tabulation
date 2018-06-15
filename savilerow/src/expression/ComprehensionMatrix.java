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
import savilerow.treetransformer.*;
import savilerow.model.*;
import savilerow.*;

public class ComprehensionMatrix extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    // One-dimensional matrix comprehension.
    // May be nested.
    public ComprehensionMatrix(ASTNode innerexp, ArrayList<ASTNode> quants, ASTNode conds) {
        super(innerexp, new Container(quants), conds, new IntegerDomain(new Range(NumberConstant.make(1), null)));
    }
    
    public ComprehensionMatrix(ASTNode innerexp, ArrayList<ASTNode> quants, ASTNode conds, ASTNode index) {
        super(innerexp, new Container(quants), conds, index);
    }
    
    public ASTNode copy()
	{
	    return new ComprehensionMatrix(getChild(0), getChild(1).getChildren(), getChild(2), getChild(3));
	}
	public boolean toFlatten(boolean propagate) { return false; }
	
	// Does it contain bools/constraints
	public boolean isRelation() {
        return getChild(0).isRelation();
    }
    public boolean isNumerical() {
        return getChild(0).isNumerical();
    }
    
	public int getDimension() {
	    return 1+getChild(0).getDimension();
	}
	
	@Override
    public boolean typecheck(SymbolTable st) {
	    if(!getChild(0).typecheck(st) || !getChild(1).typecheck(st) || !getChild(2).typecheck(st) || !getChild(3).typecheck(st))
	        return false;
	    
	    for(int i=0; i<getChild(1).numChildren(); i++) {
	        ASTNode quant=getChild(1).getChild(i);
	        if(getParent().getDomainForId(quant.getChild(0))!=null || st.hasVariable(quant.getChild(0).toString())) {
	            CmdFlags.println("ERROR: In matrix comprehension: "+this); 
                CmdFlags.println("ERROR: Variable `"+quant.getChild(0)+"' is already defined.");
                return false;
	        }
	        for(int j=0; j<i; j++) {
	            if(quant.getChild(0).equals(getChild(1).getChild(j).getChild(0))) {
	                // Defined to the left in the same comprehension.
	                CmdFlags.println("ERROR: In matrix comprehension: "+this); 
	                CmdFlags.println("ERROR: Variable `"+quant.getChild(0)+"' is already defined.");
	                return false;
	            }
	        }
	    }
	    
	    if(getChild(2).getCategory()>ASTNode.Quantifier) {
	        System.out.println("ERROR: In matrix comprehension: "+this); 
            System.out.println("ERROR: Decision variable in condition.");
            return false;
	    }
	    if(! getChild(2).isRelation()) {
	        System.out.println("ERROR: In matrix comprehension: "+this); 
            System.out.println("ERROR: The condition is not a boolean expression.");
            return false;
	    }
	    if(getChild(3).getCategory()>ASTNode.Quantifier) {
	        System.out.println("ERROR: In matrix comprehension: "+this); 
            System.out.println("ERROR: Decision variable in index domain.");
            return false;
	    }
	    if(! getChild(3).isSet()) {
	        System.out.println("ERROR: In matrix comprehension: "+this); 
            System.out.println("ERROR: Index domain is not a set.");
            return false;
	    }
	    return true;
	}
	
	@Override
	public ASTNode getDomainForId(ASTNode id) {
	    for(int i=0; i<getChild(1).numChildren(); i++) {
	        ASTNode quant=getChild(1).getChild(i);
	        if(quant.getChild(0).equals(id)) {
	            return quant.getChild(1);
	        }
	    }
	    return getParent().getDomainForId(id);
    }
    
    public Intpair getBounds() {
        return getChild(0).getBounds();  // The bounds of the inner expression will contain all the elements of the concrete matrix.
    }
    public PairASTNode getBoundsAST() {
        return getChild(0).getBoundsAST();
    }
    
    // Should never need to be output in the instance-level formats. Just Dominion and E'
    
    public void toDominionInner(StringBuilder b, boolean bool_context) {
        b.append("[");
        getChild(0).toDominion(b, false);
        b.append("|");
        
        // Quantifiers
        for(int i=0; i<getChild(1).numChildren(); i++)
        {
            getChild(1).getChild(i).toDominionParam(b);
            b.append(", ");
        }
        
        // Conditions
        getChild(2).toDominionParam(b);  // should be true if there are no conditions.
        b.append("]");
	}
	public void toDominionParam(StringBuilder b){
        b.append("[");
        getChild(0).toDominionParam(b);
        b.append("|");
        
        // Quantifiers
        for(int i=0; i<getChild(1).numChildren(); i++)
        {
            getChild(1).getChild(i).toDominionParam(b);
            b.append(", ");
        }
        
        // Conditions
        getChild(2).toDominionParam(b);  // should be true if there are no conditions.
        b.append("]");
	}
	
	public String toString() {
	    StringBuilder st=new StringBuilder();
	    st.append("[");
	    st.append(getChild(0));
	    st.append("|");
	    for(int i=0; i<getChild(1).numChildren(); i++) {
	        st.append(getChild(1).getChild(i).toString());
	        st.append(", ");
	    }
	    st.append(getChild(2));
	    st.append(" ;");
	    st.append(getChild(3));
	    st.append("]");
	    return st.toString();
	}
}
