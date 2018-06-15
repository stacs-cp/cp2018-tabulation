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
import java.math.*;
import java.io.*;
import savilerow.model.SymbolTable;
import savilerow.model.Sat;

// This division has a default value of 0 which it takes when the divisor is 0,
// thus it is never undefined. 

public class SafeDivide extends BinOp
{
    public static final long serialVersionUID = 1L;
    public SafeDivide(ASTNode l, ASTNode r)
	{
		super(l, r);
	}
	
	public ASTNode copy()
	{
	    return new SafeDivide(getChild(0), getChild(1));
	}
	
	public ASTNode simplify() {
	    
	    if(getChild(1).isConstant() && getChild(1).getValue()==0) {
	        return NumberConstant.make(0);  // Default value case.
	    }
	    
	    if(getChild(0).isConstant() && getChild(1).isConstant()) {
	        long a=getChild(0).getValue();
	        long b=getChild(1).getValue();
	        if(a%b != 0) {
	            if(b<0) {
	                CmdFlags.warning("Result of integer division is not an integer: "+this+". Using floor(a/b) semantics.");
	            }
	        }
	        
	        return NumberConstant.make(Divide.div(a,b));
	    }
	    if(getChild(1).isConstant() && getChild(1).getValue()==1) {
	        getChild(0).setParent(null);
	        return getChild(0);
	    }
	    if(getChild(1).isConstant() && getChild(1).getValue()==-1) {
	        getChild(0).setParent(null);
	        return new UnaryMinus(getChild(0));   // strength reduction
	    }
	    
	    return null;
	}
	
	public Intpair getBounds()
	{
	    Intpair a=getChild(0).getBounds();
	    Intpair b=getChild(1).getBounds();
	    
	    // Algorithm is:
	    // for both bounds of a:
	    // for all denom = max(b), min(b), 1 if 1\in b, -1 if -1\in b.
	    // Take the min and max of these (up to 8) values and the default value
	    
	    ArrayList<Long> vals=new ArrayList<Long>(9);
	    vals.add(0L);
	    
	    if(b.lower!=0) {
	        vals.add(Divide.div(a.lower, b.lower));
	        vals.add(Divide.div(a.upper, b.lower));
	    } // If b.lower is 0, then 1 is the appropriate divisor -- handled below.
	    
	    if(b.upper!=0) {
            vals.add(Divide.div(a.lower, b.upper));
            vals.add(Divide.div(a.upper, b.upper));
	    }   // If b.upper is 0, then -1 is the appropriate divisor -- handled below.
	    
	    // Denominator includes -1
	    if(b.lower<=-1 && b.upper>=-1) {
	        vals.add(Divide.div(a.lower, -1));
	        vals.add(Divide.div(a.upper, -1));
	    }
	    
	    // Denominator includes 1
	    if(b.lower<=1 && b.upper>=1) {
	        vals.add(Divide.div(a.lower, 1));
	        vals.add(Divide.div(a.upper, 1));
	    }
	    a.lower=Collections.min(vals);
	    a.upper=Collections.max(vals);
	    return lookupBounds(a);    //  Look up in FilteredDomainStore
	}
	
	public PairASTNode getBoundsAST() {
	    PairASTNode a=getChild(0).getBoundsAST();
	    
	    if(getChild(1).isConstant()) {
	        if(getChild(1).getValue()==0) {
	            return new PairASTNode(NumberConstant.make(0), NumberConstant.make(0));  // Default value.
	        }
	        ASTNode lb=new Min(new Divide(a.e1, getChild(1)), new Min(new Divide(a.e2, getChild(1)), NumberConstant.make(0)));
	        ASTNode ub=new Max(new Divide(a.e1, getChild(1)), new Max(new Divide(a.e2, getChild(1)), NumberConstant.make(0)));
	        return new PairASTNode(lb, ub);
	    }
	    else {
	        ASTNode lb=new Min(a.e1, new Min(new UnaryMinus(a.e2), NumberConstant.make(0)));  // need the - because might divide by -1.
	        ASTNode ub=new Max(a.e2, new Max(new UnaryMinus(a.e1), NumberConstant.make(0)));
	        return new PairASTNode(lb, ub);
	    }
	}
	
	public boolean toFlatten(boolean propagate) { return true;}
	public boolean isNumerical() { return true;}
    
	public void toMinionWithAuxVar(BufferedWriter b, ASTNode aux) throws IOException {
	    b.append("div_undefzero(");
	    getChild(0).toMinion(b, false);
	    b.append(", ");
	    getChild(1).toMinion(b, false);
	    b.append(", ");
	    aux.toMinion(b, false);
	    b.append(")");
	}
	
	//  WARNING -- the rest of these output methods lose the safety
	public void toDominionWithAuxVar(StringBuilder b, ASTNode aux)	{
	    b.append(CmdFlags.getCtName()+" ");
	    b.append("div(");
	    getChild(0).toDominion(b, false);
	    b.append(", ");
	    getChild(1).toDominion(b, false);
	    b.append(", ");
	    aux.toDominion(b, false);
	    b.append(")");
	}
	
	public String toString() {
	    return "("+getChild(0)+"/"+getChild(1)+")";
	}
	public void toDominionParam(StringBuilder b) {
	    assert getCategory()<=ASTNode.Quantifier;
	    b.append("Div(");
	    getChild(0).toDominionParam(b);
	    b.append(",");
	    getChild(1).toDominionParam(b);
	    b.append(")");
	}
	public void toMinizinc(StringBuilder b,  boolean bool_context) {
	    assert !bool_context;
	    b.append("(");
	    getChild(0).toMinizinc(b, false);
	    b.append(" div ");
	    getChild(1).toMinizinc(b, false);
	    b.append(")");
	}
	
	////////////////////////////////////////////////////////////////////////////
	//
	//  SAT Encoding
	
    public void toSATWithAuxVar(Sat satModel, ASTNode auxVar) throws IOException {
        satModel.ternaryEncoding(this, auxVar);
    }
    
    public boolean test(long val1, long val2, long aux) {
        if(val2==0) return aux==0;  // default value
        return Divide.div(val1, val2)==aux;
    }
    public long func(long val1, long val2) {
        if(val2==0) return 0;
        return Divide.div(val1, val2);
    }
}