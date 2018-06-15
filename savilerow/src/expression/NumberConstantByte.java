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
import java.io.*;
import java.math.*;
import savilerow.model.*;

public class NumberConstantByte extends NumberConstant {
    public static final long serialVersionUID = 1L;
    byte num;
    public NumberConstantByte(byte n) {
        super();
        num = n;
    }
    
    public ASTNode copy() {
        return new NumberConstantByte(num);
    }
    @Override
    public boolean equals(Object b) {
        if (! (b instanceof NumberConstant)) {
            return false;
        }
        return num == ((ASTNode)b).getValue();
    }
    
    @Override
    public int hashCode() {
        // Matches implementation of hashCode for NumberConstantLong
        return num;
    }

    public String toString() {
        return String.valueOf(num);
    }
    
    public long getValue() {
        return (long)num;
    }
    public ArrayList<Intpair> getIntervalSet() {
        ArrayList<Intpair> intervals = new ArrayList<Intpair>();
        intervals.add(new Intpair(num, num));
        return intervals;
    }
    public ArrayList<Intpair> getIntervalSetExp() {
	    ArrayList<Intpair> i = new ArrayList<Intpair>();
	    i.add(new Intpair(num, num));
        return i;
    }
    
    // Same methods as Identifier for sat encoding.
    public long directEncode(Sat satModel, long value) {
        return (value==num)?satModel.getTrue():(-satModel.getTrue());
    }
    public long orderEncode(Sat satModel, long value) {
        if(num<=value) {
            return satModel.getTrue();
        }
        else {
            return -satModel.getTrue();
        }
    }

    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
        b.append(String.valueOf(num));
    }
    public void toDominionParam(StringBuilder b) {
        b.append(num);
    }
    public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
        assert !bool_context;
        b.append(String.valueOf(num));
    }
    public void toMinizinc(StringBuilder b, boolean bool_context) {
        assert !bool_context;
        b.append(num);
    }
    public void toJSON(StringBuilder bf) {
        bf.append(num+"\n");
    }
}