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
import savilerow.model.*;

//   Special case of compound matrix that contains an array of integers. 

public class CompoundMatrixConst extends ASTNodeC {
    public static final long serialVersionUID = 1L;
    // One-dimensional matrix containing integers. Indexed contiguously from 1. 
    int[] data;
    
    public CompoundMatrixConst(int[] m) {
        super();
        assert m.length>0;
        data=m;    //   Assume m will not be changed by the calling function.
    }
    
    public boolean isNumerical() {
        return true;
    }
    public boolean isSet() {
        return false;
    }
    
    public ASTNode copy() {
        int[] datacopy= new int[data.length];
        System.arraycopy(data, 0, datacopy, 0, data.length);
        return new CompoundMatrixConst(datacopy);
    }
    
    public boolean toFlatten(boolean propagate) { return false; }
    
    public Intpair getBounds() {
        int lower=data[0];
        int upper=data[0];
        for (int i=1; i < data.length; i++) {
            int tmp=data[i];
            if(tmp<lower) lower=tmp;
            if(tmp>upper) upper=tmp;
        }
        return new Intpair(lower,upper);
    }
    
    public PairASTNode getBoundsAST() {
        Intpair p=getBounds();
        return new PairASTNode(NumberConstant.make(p.lower), NumberConstant.make(p.upper));
    }
    
    @Override
    public boolean typecheck(SymbolTable st) {
        return true;
	}
    
    // Assumes the dimension is the same everywhere.
    public int getDimension() {
        return 1;
    }
    
    // For a matrix literal, is it regular?
    @Override
    public boolean isRegularMatrix() {
        // If 1-dimensional, then must be regular. 
        return true;
    }
    
    // For a regular matrix literal only, get the index domains.
    public ArrayList<ASTNode> getIndexDomains() {
        ArrayList<ASTNode> tmp=new ArrayList<ASTNode>();
        tmp.add(new IntegerDomain(new Range(NumberConstant.make(1), NumberConstant.make(data.length))));
        return tmp;
    }
    
    // Much slower version for irregular matrices.
    public ArrayList<ASTNode> getIndexDomainsIrregular() {
        return getIndexDomains();
    }
    
    // ALL output methods except E' drop the index.
    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
        assert !bool_context;
        b.append("[");
        for (int i =0; i < data.length; i++) {
            b.append(String.valueOf(data[i]));
            if (i < data.length - 1) {
                b.append(", ");
            }
        }
        b.append("]");
    }
    
    public String toString() {
        StringBuilder st = new StringBuilder();
        st.append("[");
        for (int i =0; i < data.length; i++) {
            st.append(data[i]);
            
            if (i < data.length - 1) {
                st.append(", ");
            }
        }
        st.append("]");
        return st.toString();
    }
    
    public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
        b.append("[");
        for (int i =0; i < data.length; i++) {
            b.append(String.valueOf(data[i]));
            if (i < data.length - 1) {
                b.append(", ");
            }
        }
        b.append("]");
    }
    
    public void toMinizinc(StringBuilder b, boolean bool_context) {
        //toFlatzinc(b, bool_context);
    }

    public void toJSON(StringBuilder bf) {
        toJSONHeader(bf, true);
        // children
        bf.append("\"Domain\":");
        getIndexDomains().get(0).toJSON(bf);
        bf.append(",\n");
        bf.append("\"Children\": [");
        
        for (int i = 0; i < data.length; i++) {
            bf.append("\n");
            bf.append(data[i]+"\n");  //  Same as NumberConstant toJSON method.
            // not last child
            if (i < data.length - 1) {
                bf.append(",");
            }
        }
        bf.append("]\n}");
    }
    
    public boolean childrenAreSymmetric() {
        return getParent().isChildSymmetric(getChildNo());
    }
}
