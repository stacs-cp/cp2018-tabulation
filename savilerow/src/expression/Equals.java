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
import savilerow.treetransformer.*;
import savilerow.model.Sat;

// Equality between two variables or a variable and a constant (two constants would be simplified to true or false).
// Cannot represent reification or ternary numerical constraint -- see ToVariable. 

public class Equals extends BinOp
{
    public static final long serialVersionUID = 1L;
	public Equals(ASTNode l, ASTNode r) {
		super(l, r);
	}
	
	public ASTNode copy() {
	    return new Equals(getChild(0), getChild(1));
	}
	public boolean isRelation(){return true;}
	public boolean strongProp() {
	    return getChild(0).strongProp() && getChild(1).strongProp();
	}
	
	public ASTNode simplify() {
	    if(getChild(0).equals(getChild(1))) {  // If symbolically equal, return true.
	        return new BooleanConstant(true);
	    }
	    
        // If one side is the boolean negation of the other, return false.  
        // Prevents deletevars unifying  x=not(x) and causing infinite recursion of replacing x with not(x). 
        if(getChild(0) instanceof Negate && getChild(0).getChild(0).equals(getChild(1))) {
            return new BooleanConstant(false);
        }
        if(getChild(1) instanceof Negate && getChild(1).getChild(0).equals(getChild(0))) {
            return new BooleanConstant(false);
        }
        
	    if(getChild(0).isConstant() && getChild(1).isConstant()) {
	        // If equal when interpreted as integer.... (includes 1=true)
	        return new BooleanConstant( getChild(0).getValue() == getChild(1).getValue() );
	    }
	    
	    Intpair b0=getChild(0).getBounds();
	    Intpair b1=getChild(1).getBounds();
	    
	    if(b0.lower>b1.upper || b0.upper<b1.lower) {
	        return new BooleanConstant(false);  // bounds do not overlap.
	    }
	    
	    // If one child is a variable and the other a constant
	    if(getChild(0) instanceof Identifier && getChild(1).isConstant()) {
	        ASTNode domain=((Identifier)getChild(0)).getDomain();
	        if(domain.getCategory() == ASTNode.Constant) {
	            TransformSimplify ts=new TransformSimplify();
	            domain=ts.transform(domain);
                if(! domain.containsValue(getChild(1).getValue())) {
                    return new BooleanConstant(false);
                }
	        }
	    }
	    if(getChild(1) instanceof Identifier && getChild(0).isConstant()) {
	        ASTNode domain=((Identifier)getChild(1)).getDomain();
	        if(domain.getCategory() == ASTNode.Constant) {
	            TransformSimplify ts=new TransformSimplify();
	            domain=ts.transform(domain);
                if(! domain.containsValue(getChild(0).getValue())) {
                    return new BooleanConstant(false);
                }
	        }
	    }
	    
	    // Now simplify sum1=sum2 to sum1-sum2=0
	    if(getChild(0) instanceof WeightedSum && getChild(1) instanceof WeightedSum) {
	        this.detachChildren();
	        return new Equals(BinOp.makeBinOp("-", getChild(0), getChild(1)), NumberConstant.make(0));
	    }
	    
	    // It helps identical CSE if sums have no constants in them. 
	    // Shift the constant to the other side to combine with constant/param/quantifier id. 
	    if(getChild(0) instanceof WeightedSum && getChild(0).getCategory()==ASTNode.Decision && getChild(1).getCategory()<ASTNode.Decision) {
	        Pair<ASTNode, ASTNode> p1=((WeightedSum)getChild(0)).retrieveConstant();
	        if(p1!=null) {
	            getChild(1).setParent(null);
	            return new Equals(p1.getSecond(), BinOp.makeBinOp("-", getChild(1), p1.getFirst()));
	        }
	    }
	    if(getChild(1) instanceof WeightedSum && getChild(1).getCategory()==ASTNode.Decision && getChild(0).getCategory()<ASTNode.Decision) {
	        Pair<ASTNode, ASTNode> p1=((WeightedSum)getChild(1)).retrieveConstant();
	        if(p1!=null) {
	            getChild(0).setParent(null);
	            return new Equals(BinOp.makeBinOp("-", getChild(0), p1.getFirst()), p1.getSecond());
	        }
	    }
	    
	    // Factor out the GCD of a sum.
	    if(getChild(0) instanceof WeightedSum && getChild(1).isConstant()) {
	        Pair<ASTNode, ASTNode> p=((WeightedSum)getChild(0)).factorOutGCD();
	        
	        if(p!=null) {
	            long gcd=p.getFirst().getValue();
	            long c=getChild(1).getValue();
	            
	            if(c%gcd != 0) {
	                // If there is a remainder when dividing the RHS by the GCD, then the sum= cannot be satisfied (RHS will be fractional)
	                return new BooleanConstant(false);
	            }
	            
	            return new Equals(p.getSecond(), NumberConstant.make(c/gcd));
	        }
	    }
	    if(getChild(1) instanceof WeightedSum && getChild(0).isConstant()) {
	        Pair<ASTNode, ASTNode> p=((WeightedSum)getChild(1)).factorOutGCD();
	        
	        if(p!=null) {
	            long gcd=p.getFirst().getValue();
	            long c=getChild(0).getValue();
	            
	            if(c%gcd != 0) {
	                // If there is a remainder when dividing the LHS by the GCD, then the sum= cannot be satisfied (RHS will be fractional)
	                return new BooleanConstant(false);
	            }
	            
	            return new Equals(p.getSecond(), NumberConstant.make(c/gcd));
	        }
	    }
	    
	    // Constants have been removed from sums by the above. Catch x-y=0 and
	    // rearrange to x=y.
	    if(getChild(0) instanceof WeightedSum && getChild(0).numChildren()==2 && getChild(1).isConstant() && getChild(1).getValue()==0) {
	        long wt1=((WeightedSum)getChild(0)).getWeight(0);
	        long wt2=((WeightedSum)getChild(0)).getWeight(1);
	        if(wt1+wt2==0) {
	            getChild(0).detachChildren();
	            return new Equals(getChild(0).getChild(0), getChild(0).getChild(1));
	        }
	    }
	    if(getChild(1) instanceof WeightedSum && getChild(1).numChildren()==2 && getChild(0).isConstant() && getChild(0).getValue()==0) {
	        long wt1=((WeightedSum)getChild(1)).getWeight(0);
	        long wt2=((WeightedSum)getChild(1)).getWeight(1);
	        if(wt1+wt2==0) {
	            getChild(1).detachChildren();
	            return new Equals(getChild(1).getChild(0), getChild(1).getChild(1));
	        }
	    }
	    
	    return null;
	}
	
	@Override
	public boolean isNegatable() {
	    return true;
	}
	@Override
	public ASTNode negation() {
	    return new AllDifferent(getChild(0), getChild(1));
	}
	
	@Override
	public ASTNode normalise() {
	    if(getChild(0).hashCode()>getChild(1).hashCode()) {
	        detachChildren();
	        return new Equals(getChild(1), getChild(0));
	    }
	    return this;
	}
	
	@Override
	public ASTNode normaliseAlpha() {
	    if(getChild(0).toString().compareTo(getChild(1).toString())>0) {
	        detachChildren();
	        return new Equals(getChild(1), getChild(0));
	    }
	    return null;
	}
	
	public String toString() {
	    return "("+getChild(0)+"="+getChild(1)+")";
	}
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException
	{
	    assert bool_context;
	    if(getChild(0).isConstant()) {
	        if(CmdFlags.getUseBoundVars() && getChild(1).exceedsBoundThreshold() ) {
	            b.append("eq(");
	        }
	        else {
	            b.append("w-literal(");
	        }
	        getChild(1).toMinion(b, false);
	        b.append(",");
	        getChild(0).toMinion(b, false);
	        b.append(")");
	    }
	    else if(getChild(1).isConstant()) {
	        if(CmdFlags.getUseBoundVars() && getChild(0).exceedsBoundThreshold() ) {
	            b.append("eq(");
	        }
	        else {
	            b.append("w-literal(");
	        }
	        getChild(0).toMinion(b, false);
	        b.append(",");
	        getChild(1).toMinion(b, false);
	        b.append(")");
	    }
	    else {
	        if(CmdFlags.getUseBoundVars() && ( getChild(0).exceedsBoundThreshold() || getChild(1).exceedsBoundThreshold() )) {
                b.append("eq(");
            }
            else {
                b.append("gaceq(");
            }
            getChild(0).toMinion(b, false);
            b.append(",");
            getChild(1).toMinion(b, false);
            b.append(")");
	    }
	}
	public void toDominionInner(StringBuilder b, boolean bool_context)
	{
	    // literal propagates better than eq in places where it can be negated (e.g. in a reify)
	    if(getChild(0).getCategory() <= ASTNode.Quantifier) {
	        b.append(CmdFlags.getCtName()+" ");
            b.append("literal(");
            getChild(1).toDominion(b, false);
            b.append(",");
            getChild(0).toDominionParam(b);
            b.append(")");
            return;
	    }
	    if(getChild(1).getCategory() <= ASTNode.Quantifier) {
	        b.append(CmdFlags.getCtName()+" ");
            b.append("literal(");
            getChild(0).toDominion(b, false);
            b.append(",");
            getChild(1).toDominionParam(b);
            b.append(")");
            return;
	    }
	    b.append(CmdFlags.getCtName()+" ");
	    b.append("eq(");
	    getChild(0).toDominion(b, false);
	    b.append(",");
	    getChild(1).toDominion(b, false);
	    b.append(")");
	}
	public void toDominionParam(StringBuilder b) {
	    b.append("(");
	    getChild(0).toDominionParam(b);
	    b.append("=");
	    getChild(1).toDominionParam(b);
	    b.append(")");
	}
	public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
	    b.append("constraint int_eq(");
	    getChild(0).toFlatzinc(b, false);
	    b.append(",");
	    getChild(1).toFlatzinc(b, false);
	    b.append(");");
	}
	
	// Might be a problem here.. what if it contains a bool type.
	public void toMinizinc(StringBuilder b, boolean bool_context) {
	    b.append("(");
	    getChild(0).toMinizinc(b, false);
	    b.append("==");
	    getChild(1).toMinizinc(b, false);
	    b.append(")");
	}
	
	////////////////////////////////////////////////////////////////////////////
	//  SAT encoding
	
	public Long toSATLiteral(Sat satModel) {
	    if(getChild(0).isConstant()) {
	        return getChild(1).directEncode(satModel, getChild(0).getValue());
        }
        if(getChild(1).isConstant()) {
            return getChild(0).directEncode(satModel, getChild(1).getValue());
        }
        return null;
	}
	
	public void toSAT(Sat satModel) throws IOException {
	    // Support encoding just for equality. 
	    // [x!=a] \/ [y=a] for all a,  and both ways round (x and y). 
	    encodeEquality(satModel, false, 0);
	}
	
	public void toSATWithAuxVar(Sat satModel, long aux) throws IOException {
	    encodeEquality(satModel, true, aux);
	    
	    // Direct encode of the inverse constraint.
	    ArrayList<Intpair> domain1=getChild(0).getIntervalSetExp();
        ArrayList<Intpair> domain2=getChild(1).getIntervalSetExp();
        
        for (Intpair pair1 : domain1)
        {
            for (long i=pair1.lower; i<=pair1.upper; i++)
            {
                satModel.addClause(-getChild(0).directEncode(satModel, i), -getChild(1).directEncode(satModel, i), aux);
            }
        }
	}
	
	private void encodeEquality(Sat satModel, boolean auxused, long aux) throws IOException {
	    //  aux ->  var1 = var2
	    ArrayList<Intpair> domain1=getChild(0).getIntervalSetExp();
        ArrayList<Intpair> domain2=getChild(1).getIntervalSetExp();
        
        for (Intpair pair1 : domain1)
        {
            for (long i=pair1.lower; i<=pair1.upper; i++)
            {
                if(auxused) {
                    satModel.addClause(-getChild(0).directEncode(satModel, i), getChild(1).directEncode(satModel, i), -aux);
                }
                else {
                    satModel.addClause(-getChild(0).directEncode(satModel, i), getChild(1).directEncode(satModel, i));
                }
            }
        }
        
        for (Intpair pair1 : domain2)
        {
            for (long i=pair1.lower; i<=pair1.upper; i++)
            {
                if(auxused) {
                    satModel.addClause(-getChild(1).directEncode(satModel, i), getChild(0).directEncode(satModel, i), -aux);
                }
                else {
                    satModel.addClause(-getChild(1).directEncode(satModel, i), getChild(0).directEncode(satModel, i));
                }
            }
        }
	}
	
    public boolean childrenAreSymmetric() {
        return true;
    }
    
    public boolean canChildBeConvertedToDifference(int childIndex) {
        return isMyOnlyOtherSiblingEqualZero(childIndex);
    }

}