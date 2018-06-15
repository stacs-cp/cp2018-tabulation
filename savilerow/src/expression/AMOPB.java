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
import java.math.BigInteger;
import java.io.*;
import savilerow.model.SymbolTable;
import savilerow.model.Sat;

//  Pseudo-boolean with at-most-one groups constraint. 

public class AMOPB extends ASTNodeC {
    public static final long serialVersionUID = 1L;
    ArrayList<ArrayList<Long>> coeffs;   //  coefficients grouped into AMO groups. 
    long cmp;      // weighted sum <= cmp.
    
    public AMOPB(ArrayList<ArrayList<Long>> _coeffs, ASTNode[] bools, long c) {
        super(bools);
        coeffs=_coeffs;
        cmp=c;
    }
    
    public ASTNode copy() {
        return new AMOPB(coeffs, getChildrenArray(), cmp);
    }
    
    @Override
    public boolean equals(Object other) {
        if (! (other instanceof AMOPB)) {
            return false;
        }
        AMOPB oth = (AMOPB) other;
        
        if(! coeffs.equals(oth.coeffs)) {
            return false;
        }
        if (! Arrays.equals(oth.getChildrenArray(), getChildrenArray())) {
            return false;
        }
        return oth.cmp == cmp;
    }
    
    @Override
    public int hashCode() {
        if(hashCache==Integer.MIN_VALUE) {
            hashCache = 31*coeffs.hashCode() + Arrays.hashCode(getChildrenArray()) + (int)cmp;
            return hashCache;
        }
        else {
            return hashCache;
        }
    }
    
    public boolean isRelation() {
        return true;
    }
    
    //////////////////////////////////////////////////////////////////////////// 
    // 
    // Output methods.
    
    public String toString() {
        String st = "AMOPB(";
        st+=String.valueOf(coeffs)+", ";
        st+=Arrays.toString(getChildrenArray())+", ";
        return st + cmp + ")";
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //  SAT encoding
    
    public void toSAT(Sat satModel) throws IOException {
        
    }
}
