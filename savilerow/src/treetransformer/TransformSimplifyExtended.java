package savilerow.treetransformer;
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


import savilerow.expression.*;
import savilerow.model.*;
import savilerow.CmdFlags;
import java.util.*;

//  A unique one, call the simplify method on curnode -- implements lots of small rules.
//  Must be bottom up so that each node can call methods on its children knowing they
//  are well formed. e.g. not Tag. 

// This version also includes deleting variables. Rewrites the symbol table;
// must not be used on constraints that are not in the model. 

public class TransformSimplifyExtended extends TreeTransformerBottomUpNoWrapper
{
    public TransformSimplifyExtended(Model m) { super(m);}
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    // tree nodes are supposed to be immutable (apart from their child pointers), so if it has changed
	    // then it should be a new node.
	    ASTNode tmp=curnode.simplify();
	    if(tmp!=null) {
	        assert tmp!=curnode;   ///   simplify not allowed to return 'this'
	        return new NodeReplacement(tmp);
	    }
	    
	    if(CmdFlags.getUseDeleteVars()) {
	        // Similar to TransformDeleteVars in here. Except that there is no
	        // need to check SymbolTable.replacements as Identifier.simplify already
	        // does that. 
	        
            return doDeleteVars(curnode, m);
	    }
	    
	    return null;
    }
    
    private static NodeReplacement doDeleteVars(ASTNode curnode, Model m) {
        //  Top level expressions only (not expressions nested in an And inside the top level And).
        // This is to guarantee the top level And is replaced and all its children traversed again.
        if(curnode.getParent()!=null 
            && ( (curnode.getParent() instanceof And && curnode.getParent().getParent() instanceof Top)
                || curnode.getParent() instanceof Top)) {
            // Only do assignment after aggregation has finished because it prevents aggregation of allDiff. 
            boolean doAssignVar=(!CmdFlags.getUseAggregate()) || CmdFlags.getAfterAggregate();
	        // Equality types.
	        if(curnode instanceof Equals || curnode instanceof Iff || curnode instanceof ToVariable) {
	            ASTNode c0=curnode.getChild(0);
	            ASTNode c1=curnode.getChild(1);
	            if(c0 instanceof Identifier && c1.isConstant() && doAssignVar) {
	                //  Makes a big assumption: that the equality would already have simplified to false 
	                //  if the value is not in domain. 
	                m.global_symbols.assignVariable(c0, c1);
                    return new NodeReplacement(new BooleanConstant(true));
                }
                if(c1 instanceof Identifier && c0.isConstant() && doAssignVar) {
                    //  Makes a big assumption: that the equality would already have simplified to false 
	                //  if the value is not in domain.
                    m.global_symbols.assignVariable(c1, c0);
                    return new NodeReplacement(new BooleanConstant(true));
                }
	            if(c0 instanceof Identifier && c1 instanceof Identifier
	                && !(c0.equals(c1))) {
	                // Last condition makes sure the two identifiers are not the same. This can occur 
	                // when there is a loop of equalities.
	                m.global_symbols.unifyVariables(c0, c1);
	                return new NodeReplacement(new BooleanConstant(true));
	            }
	            
	            // Cases where one variable is the negation of the other
	            if(CmdFlags.getMiniontrans() || CmdFlags.getSattrans()) {
                    if(c0 instanceof Identifier && c1 instanceof Negate && c1.getChild(0) instanceof Identifier) {
                        m.global_symbols.unifyVariablesNegated(c0, c1);
                        return new NodeReplacement(new BooleanConstant(true));
                    }
                    if(c1 instanceof Identifier && c0 instanceof Negate && c0.getChild(0) instanceof Identifier) {
                        m.global_symbols.unifyVariablesNegated(c1, c0);
                        return new NodeReplacement(new BooleanConstant(true));
                    }
                }
            }
            
            // Bare or negated boolean variable in the top-level And.
            if(curnode instanceof Identifier && doAssignVar) {
                m.global_symbols.assignVariable(curnode, new BooleanConstant(true));
                return new NodeReplacement(new BooleanConstant(true));
            }
            if(curnode instanceof Negate && curnode.getChild(0) instanceof Identifier && doAssignVar) {
                m.global_symbols.assignVariable(curnode.getChild(0), new BooleanConstant(false));
                return new NodeReplacement(new BooleanConstant(true));
            }
            
            //  Put unary constraints into the domain. 
            if(curnode instanceof InSet && curnode.getChild(0) instanceof Identifier 
                && curnode.getChild(0).getCategory()==ASTNode.Decision
                && curnode.getChild(1).getCategory()==ASTNode.Constant) {
                String n=curnode.getChild(0).toString();
                m.global_symbols.setDomain(n, new Intersect(m.global_symbols.getDomain(n), curnode.getChild(1)));
                return new NodeReplacement(new BooleanConstant(true));
            }
            
            //  MultiStage has an implicit unary constraint.
            if(curnode instanceof MultiStage && curnode.getChild(0) instanceof Identifier && curnode.getChild(1).getCategory()==ASTNode.Constant) {
                ASTNode dom=((Identifier)curnode.getChild(0)).getDomain();
                if(dom.getCategory()==ASTNode.Constant) {
                    ArrayList<Intpair> listvals=new ArrayList<Intpair>();
                    
                    for(int i=1; i<curnode.getChild(1).numChildren(); i++) {
                        listvals=Intpair.union(listvals, curnode.getChild(1).getChild(i).getIntervalSetExp());
                    }
                    
                    ArrayList<Intpair> olddom=dom.getIntervalSet();
                    
                    ArrayList<Intpair> a=Intpair.intersection(olddom, listvals);
                    
                    if(! a.equals(olddom)) {
                        String n=curnode.getChild(0).toString();
                        m.global_symbols.setDomain(n, Intpair.makeDomain(a, curnode.getChild(0).isRelation()));
                    }
                }
            }
        }
        return null;
    }
}

