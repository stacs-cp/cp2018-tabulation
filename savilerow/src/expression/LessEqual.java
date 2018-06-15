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
import java.math.*;
import savilerow.model.SymbolTable;
import savilerow.treetransformer.*;
import savilerow.model.Sat;

public class LessEqual extends BinOp
{
    public static final long serialVersionUID = 1L;
	public LessEqual(ASTNode l, ASTNode r)
	{
		super(l, r);
	}
	
	public ASTNode copy()
	{
	    return new LessEqual(getChild(0), getChild(1));
	}
	public boolean isRelation(){return true;}
	public boolean strongProp() {
        return true;
    }
	
	public void toDominionInner(StringBuilder b, boolean bool_context)
	{
	    // Special case for (weighted) sumleq and sumgeq
	    // Can't both be unflattened weightedsums.
	    assert !(getChild(0) instanceof WeightedSum && getChild(1) instanceof WeightedSum);
	    
	    if(getChild(0) instanceof WeightedSum) {
	        if(getChild(0).getCategory()>ASTNode.Quantifier) {
	            ((WeightedSum)getChild(0)).toDominionLeq(b, getChild(1));
	            return;
	        }
	    }
	    if(getChild(1) instanceof WeightedSum) {
	        if(getChild(1).getCategory()>ASTNode.Quantifier) {
	            ((WeightedSum)getChild(1)).toDominionGeq(b, getChild(0));
	            return;
	        }
	    }
	    
	    b.append(CmdFlags.getCtName()+" ");
	    b.append("leq(");
	    getChild(0).toDominion(b, false);
	    b.append(", ");
	    getChild(1).toDominion(b, false);
	    b.append(")");
	}
	
	public ASTNode simplify() {
	    
	    if(getChild(0).equals(getChild(1))) return new BooleanConstant(true);
	    
	    Intpair a=getChild(0).getBounds();
	    Intpair b=getChild(1).getBounds();
	    
	    if(a.upper <= b.lower) return new BooleanConstant(true);
	    if(a.lower > b.upper) return new BooleanConstant(false);
	    
	    if(getChild(0).isConstant() && getChild(1).isConstant()) {
	        if(getChild(0).getValue()<=getChild(1).getValue()) return new BooleanConstant(true);
	        else return new BooleanConstant(false);
	    }
	    
	    // Now simplify sum1<=sum2 to sum1-sum2<=0 
	    if(getChild(0) instanceof WeightedSum && getChild(1) instanceof WeightedSum) {
	        detachChildren();
	        return new LessEqual(BinOp.makeBinOp("-", getChild(0), getChild(1)), NumberConstant.make(0));
	    }
	    
	    // Finally shift constants out of a sum to combine with a constant/param/quantifier id on the other side.
	    if(getChild(0) instanceof WeightedSum && getChild(0).getCategory()==ASTNode.Decision && getChild(1).getCategory()<ASTNode.Decision) {
	        Pair<ASTNode, ASTNode> p1=((WeightedSum)getChild(0)).retrieveConstant();
	        if(p1!=null) {
	            getChild(1).setParent(null);
	            return new LessEqual(p1.getSecond(), BinOp.makeBinOp("-", getChild(1), p1.getFirst()));
	        }
	    }
	    if(getChild(1) instanceof WeightedSum && getChild(1).getCategory()==ASTNode.Decision && getChild(0).getCategory()<ASTNode.Decision) {
	        Pair<ASTNode, ASTNode> p1=((WeightedSum)getChild(1)).retrieveConstant();
	        if(p1!=null) {
	            getChild(0).setParent(null);
	            return new LessEqual(BinOp.makeBinOp("-", getChild(0), p1.getFirst()), p1.getSecond());
	        }
	    }
	    
	    // Factor out the GCD of a sum.
	    if(getChild(0) instanceof WeightedSum && getChild(1).isConstant()) {
	        Pair<ASTNode, ASTNode> p=((WeightedSum)getChild(0)).factorOutGCD();
	        
	        if(p!=null) {
	            long gcd=p.getFirst().getValue();
	            long c=getChild(1).getValue();
	            
	            // Sum is on the left so need to round downwards when calculating c/gcd.
	            long rhs=Divide.div(c, gcd);
	            
	            return new LessEqual(p.getSecond(), NumberConstant.make(rhs));
	        }
	    }
	    if(getChild(1) instanceof WeightedSum && getChild(0).isConstant()) {
	        Pair<ASTNode, ASTNode> p=((WeightedSum)getChild(1)).factorOutGCD();
	        
	        if(p!=null) {
	            long gcd=p.getFirst().getValue();
	            long c=getChild(0).getValue();
	            
	            // Sum is on the right so need to round upwards when calculating c/gcd.
	            //  4<= 3x+3y   becomes   1.33 <= x+y  becomes   2<=x+y
	            long lhs=Divide.divceil(c, gcd);
	            
	            return new LessEqual(NumberConstant.make(lhs), p.getSecond());
	        }
	    }
	    
	    return null;
	}
	
	
    /* ====================================================================
     toFlatten(boolean propagate)
     Overrides the default in ASTNode to change behaviour with SAT backend.
    ==================================================================== */
    
    @Override
    public boolean toFlatten(boolean propagate) {
        if(CmdFlags.getSattrans() && !propagate) {
            ASTNode p = getParent();
            // SAT. Flatten expressions that are not top-level and do not have a single literal encoding.
            if(p instanceof Top || (p instanceof And && (p.getParent() instanceof Top))) {
                return false;
            }
            // Exclude expressions that are encoded as a single SAT literal.
            if( ( getChild(0).isConstant() && getChild(1) instanceof Identifier ) || (getChild(1).isConstant() && getChild(0) instanceof Identifier) ) {
                return false;
            }
            return true;
        }
        //  Revert to the same method on the superclass.
        return super.toFlatten(propagate);
    }
	
	@Override
	public boolean isNegatable() {
	    return true;
	}
	@Override
	public ASTNode negation() {
	    return new Less(getChild(1), getChild(0));
	}
	
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException
	{
	    assert bool_context;
	    // Special case for (weighted) sumleq and sumgeq
	    // Can't both be unflattened weightedsums.
	    assert !(getChild(0) instanceof WeightedSum && getChild(1) instanceof WeightedSum);
	    
	    if(getChild(0) instanceof WeightedSum) {
	        ((WeightedSum)getChild(0)).toMinionLeq(b, getChild(1));
	        return;
	    }
	    if(getChild(1) instanceof WeightedSum) {
	        ((WeightedSum)getChild(1)).toMinionGeq(b, getChild(0));
	        return;
	    }
	    
	    
	    b.append("ineq(");
	    getChild(0).toMinion(b, false);
	    b.append(", ");
	    getChild(1).toMinion(b, false);
	    b.append(", 0)");
	}
	
	public void toDominionParam(StringBuilder b) {
	    b.append("(");
	    getChild(0).toDominionParam(b);
	    b.append("<=");
	    getChild(1).toDominionParam(b);
	    b.append(")");
	    
	}
	public String toString() {
	    return "("+getChild(0)+"<="+getChild(1)+")";
	}
	
	public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
	    if(getChild(0) instanceof WeightedSum) {
	        ((WeightedSum)getChild(0)).toFlatzincLeq(b, getChild(1));
	        return;
	    }
	    if(getChild(1) instanceof WeightedSum) {
	        ((WeightedSum)getChild(1)).toFlatzincGeq(b, getChild(0));
	        return;
	    }
	    
	    b.append("constraint int_le(");
	    getChild(0).toFlatzinc(b, false);
	    b.append(", ");
	    getChild(1).toFlatzinc(b, false);
	    b.append(");");
	}
	
	public void toMinizinc(StringBuilder b, boolean bool_context) {
	    b.append("(");
	    getChild(0).toMinizinc(b, false);
	    b.append("<=");
	    getChild(1).toMinizinc(b, false);
	    b.append(")");
	}
	
	////////////////////////////////////////////////////////////////////////////
	//  SAT encodings
	
	//  Support encoding seems better than order encoding, in informal experiment with Black Hole
	
	public Long toSATLiteral(Sat satModel) {
	    if(getChild(0).isConstant()) {
	        if(getChild(1) instanceof SATLiteral) {
	            assert getChild(0).getValue()==1;   // The only sensible value. If it's anything else, simplify is incomplete.
	            return ((SATLiteral)getChild(1)).getLit();  // 1<=b  rewrites to b
	        }
	        else if(getChild(1) instanceof Identifier) {
	            return -satModel.getOrderVariable(getChild(1).toString(), getChild(0).getValue()-1);
	        }
        }
        if(getChild(1).isConstant()) {
            if(getChild(0) instanceof SATLiteral) {
	            assert getChild(1).getValue()==0;
	            return -((SATLiteral)getChild(0)).getLit();  // b<1  rewrites to -b
	        }
	        else if(getChild(0) instanceof Identifier) {   // Could also be a sum.
	            return satModel.getOrderVariable(getChild(0).toString(), getChild(1).getValue());
	        }
        }
        return null;
	}
	
	static boolean useOrderEnc=true;
	
    public void toSAT(Sat satModel) throws IOException {
        // Special case for (weighted) sumleq and sumgeq
        // Can't both be unflattened weightedsums.
        assert !(getChild(0) instanceof WeightedSum && getChild(1) instanceof WeightedSum);
        if (getChild(0) instanceof WeightedSum) {
            ((WeightedSum) getChild(0)).toSATLeq(satModel, getChild(1).getValue());
        } else if (getChild(1) instanceof WeightedSum) {
            ((WeightedSum) getChild(1)).toSATGeq(satModel, getChild(0).getValue());
        }
        else {
            if(useOrderEnc) {
                toSATOrderEnc(satModel, 0);
            }
            else {
                satModel.supportEncodingBinary(this,getChild(0),getChild(1));
            }
        }
    }
    
    public void toSATWithAuxVar(Sat satModel, long aux) throws IOException {
        
        if (getChild(0) instanceof WeightedSum) {
            ((WeightedSum) getChild(0)).toSATLeqWithAuxVar(satModel, getChild(1).getValue(), aux);
        } else if (getChild(1) instanceof WeightedSum) {
            ((WeightedSum) getChild(1)).toSATGeqWithAuxVar(satModel, getChild(0).getValue(), aux);
        } else {
            if(useOrderEnc) {
                toSATOrderEnc(satModel, -aux);
                // Construct the negation
                (new Less(getChild(1), getChild(0))).toSATOrderEnc(satModel, aux);
            }
            else {
                satModel.supportEncodingBinaryWithAuxVar(this,getChild(0),getChild(1),aux);
            }
        }
    }
    
    public void toSATOrderEnc(Sat satModel, long aux) throws IOException {
        ArrayList<Intpair> a=getChild(0).getIntervalSetExp();
        a=Intpair.union(a, getChild(1).getIntervalSetExp());
        
        for(Intpair pair1 : a) {
            for (long i=pair1.lower; i<=pair1.upper; i++) {
                if(aux!=0) {
                    satModel.addClause(getChild(0).orderEncode(satModel, i), -getChild(1).orderEncode(satModel, i), aux);
                }
                else {
                    satModel.addClause(getChild(0).orderEncode(satModel, i), -getChild(1).orderEncode(satModel, i));
                }
            }
        }
    }
    
    public boolean test(long value1, long value2)
    {
        return value1<=value2;
    }
}