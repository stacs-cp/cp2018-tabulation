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
import savilerow.model.Sat;

//  UNFINISHED

// Renewable resource constraint.
// First argument is array of start time variables
// Second argument is durations of each task
// Third argument is the resource requirements of each task
// Fourth argument is the resource consumption limit at all time steps. 

public class Cumulative extends ASTNodeC {
    public static final long serialVersionUID = 1L;
    public Cumulative(ASTNode start, ASTNode dur, ASTNode res, ASTNode limit) {
        super(start, dur, res, limit);
    }
    
    public ASTNode copy() {
        return new Cumulative(getChild(0), getChild(1), getChild(2), getChild(3));
    }
    
    public boolean isRelation() { return true; }
    
    public boolean typecheck(SymbolTable st) {
        for(int i=0; i<4; i++) {
            if(!getChild(i).typecheck(st)) {
                return false;
            }
        }
        if (getChild(0).getDimension() != 1) {
            CmdFlags.println("ERROR: Expected one-dimensional matrix in first argument of cumulative: " + this);
            return false;
        }
        if (getChild(1).getDimension() != 1) {
            CmdFlags.println("ERROR: Expected one-dimensional matrix in second argument of cumulative: " + this);
            return false;
        }
        if (getChild(2).getDimension() != 1) {
            CmdFlags.println("ERROR: Expected one-dimensional matrix in third argument of cumulative: " + this);
            return false;
        }
        if(getChild(3).getDimension()!=0) {
            CmdFlags.println("ERROR: Expected scalar in fourth argument of cumulative: " + this);
            return false;
        }
        
        return true;
    }
    
    public ASTNode simplify() {
        
        return null;
    }

    @Override
    public boolean isNegatable() {
        return getChild(0) instanceof CompoundMatrix && getChild(0).numChildren() == 3;
    }
    @Override
    public ASTNode negation() {
        assert getChild(0) instanceof CompoundMatrix && getChild(0).numChildren() == 3;
        return new Equals(getChild(0).getChild(1), getChild(0).getChild(2));
    }

    public ASTNode normalise() {
        // sort by hashcode
        if (!(getChild(0) instanceof CompoundMatrix)) {
            return this;
        }
        
        ArrayList<ASTNode> ch = getChild(0).getChildren(1);
        
        boolean changed = sortByHashcode(ch);
        if (changed) {
            return new AllDifferent(new CompoundMatrix(ch));
        } else {
            return this;
        }

    }

    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
        assert bool_context;
        assert numChildren() == 1;
        ASTNode ch = getChild(0);
        if (ch instanceof CompoundMatrix && ch.numChildren() == 3) {
            b.append("diseq(");
            ch.getChild(1).toMinion(b, false);
            b.append(",");
            ch.getChild(2).toMinion(b, false);
            b.append(")");
        } else {
            String ctname = "gacalldiff";
            if (ch instanceof CompoundMatrix) {
                for (int i =1; i < ch.numChildren(); i++) {
                    if (CmdFlags.getUseBoundVars() && ch.getChild(i).exceedsBoundThreshold()) {
                        ctname = "alldiff";
                        break;
                    }
                }
            }

            b.append(ctname);
            b.append("(");
            getChild(0).toMinion(b, false);
            b.append(")");
        }
    }
    public void toDominionParam(StringBuilder b) {
        assert getChild(0) instanceof CompoundMatrix;
        assert getChild(0).numChildren() == 3;
        b.append("(");
        getChild(0).getChild(1).toDominionParam(b);
        b.append("!=");
        getChild(0).getChild(2).toDominionParam(b);
        b.append(")");
    }
    public void toDominionInner(StringBuilder b, boolean bool_context) {
        if (getCategory() <= ASTNode.Quantifier) {
            toDominionParam(b);            // Wot if it's inside an and or something?? it won't accept a non-constraint argument.
            return;
        }
        assert numChildren() == 1;
        ASTNode ch = getChild(0);
        b.append(CmdFlags.getCtName() + " ");
        if (ch instanceof CompoundMatrix && ch.numChildren() == 3) {
            b.append("noteq(");
            ch.getChild(1).toDominion(b, false);
            b.append(",");
            ch.getChild(2).toDominion(b, false);
            b.append(")");
        } else {
            b.append("alldiff(flatten(");
            getChild(0).toDominion(b, false);
            b.append("))");
        }
    }
    public String toString() {
        if (getChild(0) instanceof CompoundMatrix && getChild(0).numChildren() == 3) {
            return "(" + getChild(0).getChild(1) + " != " + getChild(0).getChild(2) + ")";
        }
        return "allDiff(" + getChild(0) + ")";
    }
    public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
        assert numChildren() == 1;
        ASTNode ch = getChild(0);
        if (ch instanceof CompoundMatrix && ch.numChildren() == 3) {
            b.append("constraint int_ne(");            /// This case will work with reification
            ch.getChild(1).toFlatzinc(b, false);
            b.append(",");
            ch.getChild(2).toFlatzinc(b, false);
            b.append(");");
        } else {
            b.append("constraint all_different_int(");            /// This case will not work with reification -- decompose alldiff before getting here.
            getChild(0).toFlatzinc(b, false);
            b.append(")::domain;");
        }
    }
    public void toMinizinc(StringBuilder b, boolean bool_context) {
        ASTNode ch = getChild(0);
        if (ch instanceof CompoundMatrix && ch.numChildren() == 3) {
            b.append("(");
            ch.getChild(1).toMinizinc(b, false);
            b.append("!=");
            ch.getChild(2).toMinizinc(b, false);
            b.append(")");
        } else {
            b.append("all_different(");
            getChild(0).toMinizinc(b, false);
            b.append(")");
        }
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //   SAT encoding of binary not-equal only. Longer AllDifferents should be
    //   decomposed before output. 
    
    public Long toSATLiteral(Sat satModel) {
        assert getChild(0).numChildren()==3;
        ASTNode ch0=getChild(0).getChild(1);
        ASTNode ch1=getChild(0).getChild(2);
        
	    if(ch0.isConstant()) {
	        return -ch1.directEncode(satModel, ch0.getValue());
        }
        if(ch1.isConstant()) {
            return -ch0.directEncode(satModel, ch1.getValue());
        }
        return null;
	}
    
    public void toSAT(Sat satModel) throws IOException
    {
        assert getChild(0).numChildren()==3;
        //  Direct encoding of pairwise not-equal constraints.
        ASTNode ch = getChild(0);
        for (int i=1; i < ch.numChildren(); i++) {
            for (int j=i+1; j<ch.numChildren(); j++) {
                //satModel.supportEncodingBinary(this, ch.getChild(i), ch.getChild(j));
                satModel.directEncoding(this, ch.getChild(i), ch.getChild(j));
            }
        }
    }
    
    public void toSATWithAuxVar(Sat satModel, long reifyVar) throws IOException {
        assert getChild(0).numChildren()==3;
        
        new Equals(getChild(0).getChild(1), getChild(0).getChild(2)).toSATWithAuxVar(satModel, -reifyVar);
    }
    
    //   Test function represents binary not-equals
    public boolean test(long val1, long val2) {
        return val1!=val2;
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //  JSON output for symmetry detection
    
    public void toJSON(StringBuilder bf) {
        toJSONHeader(bf, true);
        // children
        bf.append("\"Children\": [");
        if(getChild(0) instanceof CompoundMatrix && getChild(0).numChildren()==3) {
            //   Special case for binary != constraint.
            getChild(0).getChild(1).toJSON(bf);
            bf.append(", ");
            getChild(0).getChild(2).toJSON(bf);
        }
        else {
            // Same as toJSON method in ASTNode.
            for (int i = 0; i < numChildren(); i++) {
                bf.append("\n");
                getChild(i).toJSON(bf);
                // not last child
                if (i < numChildren() - 1) {
                    bf.append(",");
                }
            }
        }
        bf.append("]\n}");
    }
    
    public boolean childrenAreSymmetric() {
        return (getChild(0) instanceof CompoundMatrix && getChild(0).numChildren()==3);
    }
    
    public boolean isChildSymmetric(int childIndex) {
        // If not a binary != ct, then the matrix inside should be regarded as symmetric.
        return !(getChild(0) instanceof CompoundMatrix && getChild(0).numChildren()==3);
    }

    public boolean canChildBeConvertedToDifference(int childIndex) {
        return isMyOnlyOtherSiblingEqualZero(childIndex);
    }

}
