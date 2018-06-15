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

import savilerow.*;
import savilerow.expression.*;
import savilerow.model.*;
import savilerow.eprimeparser.EPrimeReader;

import java.util.*;

//  Turn MakeTable type into tableshort constraint BEFORE unrolling quantifiers.
//  Extends TransformMakeTable to inherit methods.

public class TransformMakeTableEarly extends TransformMakeTable
{
    private static boolean verbose=false;
    
    
    public TransformMakeTableEarly(Model _m) {
      super(_m);
    }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof MakeTable) {
	        if(CmdFlags.make_short_tab==0) {
	            //  Option 0 given on command line. 
	            //  Just throw away the MakeTable function
	            return new NodeReplacement(curnode.getChild(0));
	        }
	        
	        if(expressionInvariantExceptVars(curnode.getChild(0), curnode.getChild(0))) {
	            boolean shorttable=(CmdFlags.make_short_tab==2 || CmdFlags.make_short_tab==4);
                RetPair ret = tryCache(curnode, shorttable);
                if(ret.nodereplace != null) {
                    return ret.nodereplace;
                }
                
                if(verbose) { 
                    System.out.println(curnode);
                    System.out.println(getVariables(curnode));
                    System.out.println(getDomains(getVariables(curnode)));
                }
                
                if(CmdFlags.make_short_tab==1 || CmdFlags.make_short_tab==3) {
                    //  Make conventional table constraint
                    ASTNode newTable = makeTableLong(curnode.getChild(0), Long.MAX_VALUE, Long.MAX_VALUE);
                    saveToCache(ret.expstring, curnode, newTable);
                    return new NodeReplacement(newTable);
                }
                else if(CmdFlags.make_short_tab==2 || CmdFlags.make_short_tab==4) {
                    //  Make short table constraint.
                    ASTNode newTable = makeTableShort(curnode.getChild(0), Long.MAX_VALUE, Long.MAX_VALUE, Long.MAX_VALUE);
                    saveToCache(ret.expstring, curnode, newTable);
                    return new NodeReplacement(newTable);
                }
            }
        }
        
        return null;
    }
    
    // Check if quantifier variables will affect the table.
    //  No quantifier variables are allowed anywhere except in the indices of a matrix deref that is indexing into a matrix of decision variables. 
    public boolean expressionInvariantExceptVars(ASTNode top_exp, ASTNode exp) {
        if(exp instanceof MatrixSlice) {
            // Not allowing this.
            return false;
        }
        else if(exp instanceof MatrixDeref || exp instanceof SafeMatrixDeref) {
            //  Two cases. (1) Allow a constant matrix on the left, and recursively check the index expressions,
            //  OR  (2) decision variable matrix on the left, and anything is allowed for the indices
            if(exp.getChild(0).getCategory()==ASTNode.Constant) {
                for(int i=1; i<exp.numChildren(); i++) {
                    if(!expressionInvariantExceptVars(top_exp, exp.getChild(i))) {
                        return false;
                    }
                }
                return true;
            }
            else {
                // Here we are allowed quantifier variables in indices. In fact we don't care what the indices are.
                //  Not allowing anything complex on the left of the deref.
                if(! (exp.getChild(0) instanceof Identifier)) {
                    return false;
                }
                if(exp.getChild(0).getCategory()<ASTNode.Decision) {
                    return false;
                }
                return true;
            }
        }
        else if(exp instanceof Identifier) {
            if(exp.getCategory()==ASTNode.Quantifier) {
                // Check if the quantifier that defines exp is within top_exp or outside. 
                // If it is outside then this expression is not invariant.
                ASTNode p=top_exp.getDomainForId(exp);   // Go up from top_exp looking for the defining quantifier.
                
                return p==null;   // If the defining quantifier is within top_exp, p is null.
            }
            return true;  // A decision variable.
        }
        else {
            for(int i=0; i<exp.numChildren(); i++) {
                if(!expressionInvariantExceptVars(top_exp, exp.getChild(i))) {
                    return false;
                }
            }
            return true;
        }
    }
    
    //  Replace getVariables to collect matrix derefs.
    public ArrayList<ASTNode> getVariables(ASTNode exp) {
        HashSet<ASTNode> tmp=new HashSet<ASTNode>();
        getVariablesInner(exp, tmp);
        return new ArrayList<ASTNode>(tmp);
    }
    
    private void getVariablesInner(ASTNode exp, HashSet<ASTNode> varset) {
        if(exp instanceof Identifier && exp.getCategory()==ASTNode.Decision) {
            // Collect all decision variable identifiers -- exclude those that refer to a constant matrix and quantifier vars.
            varset.add(exp);
        }
        else if( (exp instanceof MatrixDeref || exp instanceof SafeMatrixDeref) ) {
            if(exp.getChild(0).getCategory()==ASTNode.Constant) {
                for(int i=1; i<exp.numChildren(); i++) {   //  Recurse for indices.
                    getVariablesInner(exp.getChild(i), varset);
                }
            }
            else {
                varset.add(exp);
                // Don't recurse into the matrix deref.
            }
        }
        else {
            for(int i=0; i<exp.numChildren(); i++) {
                getVariablesInner(exp.getChild(i), varset);
            }
        }
    }
    
    //  Replace getDomains to fetch domains of matrix derefs. 
    public ArrayList<ASTNode> getDomains(ArrayList<ASTNode> varlist) {
        ArrayList<ASTNode> vardoms=new ArrayList<ASTNode>();
        
        for(int i=0; i<varlist.size(); i++) {
            if(varlist.get(i) instanceof Identifier) {
                vardoms.add(m.global_symbols.getDomain(varlist.get(i).toString()));
            }
            else {
                assert varlist.get(i).getChild(0) instanceof Identifier;
                vardoms.add(m.global_symbols.getDomain(varlist.get(i).getChild(0).toString()).getChild(0));   //  Grab the base domain out of the matrix domain.
            }
        }
        return vardoms;
    }
    
}
