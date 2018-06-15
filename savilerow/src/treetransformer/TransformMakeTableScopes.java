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

//  Collect constraints with same scopes
//  Attempt to run tabulator on groups of constraints on same scope. 

public class TransformMakeTableScopes extends TreeTransformerBottomUpNoWrapper
{
    TransformMakeTable tmt;
    public TransformMakeTableScopes(Model _m, TransformMakeTable _tmt) {
        super(_m);
        tmt=_tmt;
        scopeslist=new HashMap<ArrayList<ASTNode>, ArrayList<ASTNode>>();
    }
    
    //  Map from scopes in order to list of cosntraints with that scope.
    HashMap<ArrayList<ASTNode>, ArrayList<ASTNode>> scopeslist;
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if( !(curnode instanceof And) && curnode.getParent()!=null && curnode.getParent().inTopAnd() 
            && !(curnode instanceof Tag) && curnode.isRelation()
            && !(curnode instanceof Table) && !(curnode instanceof TableShort) && !(curnode instanceof NegativeTable)) {
            
            // Get the scope. 
            ArrayList<ASTNode> scope=tmt.getVariablesOrdered(curnode);
            ASTNode.sortByAlpha(scope);  //  Sort alphabetically
            
            if(! scopeslist.containsKey(scope)) {
                scopeslist.put(scope, new ArrayList<ASTNode>());
            }
            
            scopeslist.get(scope).add(curnode);
        }
        return null;
    }
    
    //   To be called after the tree traversal when scopeslist is populated.
    //   A conversion is attempted of any set of constraints with same scope.
    public void doIt() {
        boolean shorttable=(CmdFlags.make_short_tab==2 || CmdFlags.make_short_tab==4);
        
        for(Map.Entry<ArrayList<ASTNode>,ArrayList<ASTNode>> p : scopeslist.entrySet()) {
            ArrayList<ASTNode> ctlist=p.getValue();
            if(ctlist.size()>1) {
                ASTNode totabulate=new And(ctlist);
                
                if(TransformMakeTable.verbose) {
                    System.out.println("H4");
                    System.out.println("Trying ct:"+totabulate);
                }
                
                //  Check the cache.
                TransformMakeTable.RetPair ret = tmt.tryCacheNormalised(totabulate, shorttable);
                if(ret.nodereplace != null) {
                    replaceConstraintSet(ctlist, ret.nodereplace.current_node);
                    continue;
                }
                if(tmt.failCache.contains(ret.expstring)) {   /// Ideally this check should go above the pcache check.
                    continue;
                }
                
                ASTNode a = tmt.normalise(totabulate);
                ASTNode newTable;
                if(CmdFlags.make_short_tab==3) {
                    newTable=tmt.makeTableLong(a, 10000, 100000);
                }
                else {
                    newTable=tmt.makeTableShort(a, 10000, 100000, 100000);
                }
                
                if(newTable==null) {
                    tmt.failCache.add(ret.expstring);
                    if(TransformMakeTable.verbose) {
                        System.out.println("Adding to failCache:"+ret.expstring);
                    }
                }
                else {
                    // Save in the cache
                    tmt.saveToCacheNormalised(ret.expstring, a, newTable);
                    
                    replaceConstraintSet(ctlist, newTable);
                }
            }
        }
    }
    
    private void replaceConstraintSet(ArrayList<ASTNode> ctlist, ASTNode replacement) {
        ASTNode a=ctlist.get(0);
        
        a.getParent().setChild(a.getChildNo(), replacement);
        
        //  Clear the rest of the constraints.
        for(int i=1; i<ctlist.size(); i++) {
            a=ctlist.get(i);
            a.getParent().setChild(a.getChildNo(), new BooleanConstant(true));
        }
    }
}
