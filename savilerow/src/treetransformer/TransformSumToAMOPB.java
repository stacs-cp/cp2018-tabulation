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

import java.util.ArrayList;
import java.util.HashMap;

//   Catch cases where AMO-PB encoding can be used. At the moment this is very
//   basic. 

public class TransformSumToAMOPB extends TreeTransformerBottomUpNoWrapper
{
    public TransformSumToAMOPB() { super(null); }
    
    protected NodeReplacement processNode(ASTNode curnode)
    {
        //System.out.println(curnode);
	    if(curnode instanceof LessEqual && curnode.getChild(0) instanceof WeightedSum && curnode.getChild(1).isConstant()) {
	        //  Check for all positive coefficients and all non-negative variable domains. 
	        System.out.println("    "+curnode);
	        boolean allnonneg=true;
	        WeightedSum s=(WeightedSum) curnode.getChild(0);
	        for(int i=0; i<s.numChildren(); i++) {
	            long w=s.getWeight(i);
	            assert w!=0;
	            if(w<0) {
	                allnonneg=false;
	                break;
	            }
	            Intpair bnds=s.getChild(i).getBounds();
	            if(bnds.lower<0) {
	                allnonneg=false;
	                break;
	            }
	        }
	        
	        //System.out.println(curnode+"  "+allnonneg);
	        
	        if(allnonneg) {
	            //  Parameters of the AMOPB constraint.
	            ArrayList<ArrayList<Long>> coeffs=new ArrayList<ArrayList<Long>>();
	            ArrayList<ASTNode> bools=new ArrayList<ASTNode>();
	            long cmp=curnode.getChild(1).getValue();   //  coeffs * bools <= cmp.
	            
	            ArrayList<ASTNode> ch=s.getChildren();
	            ArrayList<Long> wts=s.getWeights();
	            
	            for(int i=0; i<ch.size(); i++) {
	                if(ch.get(i)==null) {
	                    continue;   //  This element has been deleted
	                }
	                
	                //  Case one. The sum directly contains a decision variable.
	                //  Get the domain, remove the smallest value 
	                if(ch.get(i) instanceof Identifier) {
	                    ArrayList<Intpair> dom=ch.get(i).getIntervalSetExp();
	                    long coeff=wts.get(i);
	                    // chop the smallest value. 
	                    long smallestval=dom.get(0).lower;
	                    
	                    ArrayList<Long> coeffs_onevar=new ArrayList<Long>();
	                    ArrayList<ASTNode> bools_onevar=new ArrayList<ASTNode>();
	                    
	                    for(int j=0; j<dom.size(); j++) {
	                        for(long k=dom.get(j).lower; k<=dom.get(j).upper; k++) {
	                            if(k!=smallestval) {
	                                coeffs_onevar.add((coeff*k)-(coeff*smallestval));
	                                bools_onevar.add(new Equals(ch.get(i), NumberConstant.make(k)));
	                            }
	                        }
	                    }
	                    
	                    //  Adjust the other side of the binop to subtract the smallest val. 
	                    cmp -= smallestval*coeff;
	                    
	                    //  Add to the coeffs and bools.
	                    coeffs.add(coeffs_onevar);
	                    bools.addAll(bools_onevar);
	                }
	                else if(ch.get(i).isConstant()) {
	                    long val=ch.get(i).getValue()*wts.get(i);
	                    cmp -= val;  //  Move to the other side of the <=.
	                }
	                else {
	                    System.out.println("blah"+ch.get(i));
	                    return null;
	                }
                }
	            
	            return new NodeReplacement(new AMOPB(coeffs, bools.toArray(new ASTNode[bools.size()]), cmp));
	        }
	    }
	    return null;
    }
}

