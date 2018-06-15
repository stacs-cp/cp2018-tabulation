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
import savilerow.treetransformer.*;


public class ForallExpression extends Quantifier
{
    public static final long serialVersionUID = 1L;
    public ForallExpression(ASTNode i, ASTNode d, ASTNode e) {
        super(i,d,e);
    }
    
	public ASTNode copy()
	{
	    return new ForallExpression(getChild(0), getChild(1), getChild(2));
	}
	public boolean isRelation(){return true;}
	
	public String toString() {
	    return "(forall "+getChild(0)+" : "+getChild(1)+" . "+getChild(2)+")";
	}
	
	public ASTNode simplify() {
	    
	    // If the contained expression has simplified to true.
	    if(getChild(2) instanceof BooleanConstant && getChild(2).getValue()==1) {
	        // Always true by left identity of And, regardless of whether the domain is empty/condition ever satisfied. 
	        return new BooleanConstant(true);
	    }
	    // If the contained expression is false, the quantifier could be true or false depending on whether there are
	    // any iterations. 
	    
	    if(getChild(1) instanceof SimpleDomain && getChild(1).getCategory()==ASTNode.Constant
	        && !CmdFlags.getDominiontrans() ) {
	        
	        // If the domain is large, don't unroll. Also, if it contains a MakeTable function, don't unroll. 
	        Intpair dombnds=getChild(1).getBounds();
	        if(dombnds.lower+100 >= dombnds.upper  &&  !checkMakeTable(this)) {
                // Unroll it. This is supposed to be an optimisation to speed up TransformQuantifiedExpression by helping
                // TQE to simplify while unrolling.
                
                ArrayList<Long> qvals=getChild(1).getValueSet();
                ArrayList<ASTNode> expansion=new ArrayList<ASTNode>();
                for(int i=0; i<qvals.size(); i++)
                {
                    ASTNode unfoldedExpression=getChild(2).copy();
                    
                    // Sub in the value. 
                    ReplaceASTNode t=new ReplaceASTNode(getChild(0), NumberConstant.make(qvals.get(i)));
                    unfoldedExpression=t.transform(unfoldedExpression);
                    
                    expansion.add(unfoldedExpression);
                }
                
                return new And(expansion);
            }
	    }
	    
	    return null;
	}
	
	//  Look for MakeTable function in here. If found, return true. 
	boolean checkMakeTable(ASTNode a) {
	    if(a instanceof MakeTable) {
	        return true;
	    }
	    for(int i=0; i<a.numChildren(); i++) {
	        if(checkMakeTable(a.getChild(i))) return true;
	    }
	    return false;
	}
	
	public void toDominionParam(StringBuilder b) {
	    b.append("Min([");
	    getChild(2).toDominionParam(b);
	    b.append("|");
	    
	    //ArrayList<ASTNode> ids=getChild(0).getChildren();
	    //for(int i=0; i<ids.size(); i++) {
	        getChild(0).toDominionParam(b);
	        b.append(" in {");
	        getChild(1).toDominionParam(b);  // The only change from original ForallExpression.
	        b.append("}");
	        //if(i<ids.size()-1) b.append(", ");
	    //}
	    if(getChild(2) instanceof Implies && getChild(2).getChild(0).getCategory()<=ASTNode.Quantifier) {
	        b.append(", ");
	        ASTNode c=getChild(2).getChild(0);
	        if(c instanceof And) {
	            for(int i=0; i<c.numChildren(); i++) {
	                c.getChild(i).toDominionParam(b);
	                if(i<c.numChildren()-1) b.append(", ");
	            }
	        }
	        else {
	            getChild(2).getChild(0).toDominionParam(b);  // output the single condition.
	        }
	    }
	    // What about child 3???!
	    b.append("])");
	}
	
	public void toDominionInner(StringBuilder b, boolean bool_context) {
	    if(!getParent().inTopAnd()) {
	        b.append(CmdFlags.getCtName()+" ");
	        b.append("and(");
	    }
	    b.append("[");
	    boolean conditions=false;
	    if(getChild(2) instanceof Implies && getChild(2).getChild(0).getCategory()<=ASTNode.Quantifier) {
	        getChild(2).getChild(1).toDominion(b, true);
	        conditions=true;
	    }
	    else {
	        getChild(2).toDominion(b, true);
	    }
	    b.append(" | ");
	    ArrayList<ASTNode> ids=getChild(0).getChildren();
	    //for(int i=0; i<ids.size(); i++) {
	        //ids.get(i).toDominionParam(b);
	        getChild(0).toDominionParam(b);
	        b.append(" in {");
	        getChild(1).toDominionParam(b);  // The only change from original ForallExpression.
	        b.append("}");
	        //if(i<ids.size()-1) b.append(", ");
	    //}
	    if(conditions) {
	        b.append(", ");
	        ASTNode c=getChild(2).getChild(0);
	        if(c instanceof And) {
	            for(int i=0; i<c.numChildren(); i++) {
	                c.getChild(i).toDominionParam(b);
	                if(i<c.numChildren()-1) b.append(", ");
	            }
	        }
	        else {
	            getChild(2).getChild(0).toDominionParam(b);  // output the single condition.
	        }
	    }
	    b.append("]");
	    if(!getParent().inTopAnd()) { b.append(")"); }
	}
	@Override 
	public boolean inTopConjunction() {
	    return getParent().inTopConjunction();
	}
}
