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
import savilerow.model.*;

// Takes list, numbers of occurrences, and values.
// Constrains the number of occurrences of the value in the list to be at most occ.

public class AtMost extends ASTNodeC {
    public static final long serialVersionUID = 1L;
    public AtMost(ASTNode v, ASTNode occ, ASTNode val) {
        super(v, occ, val);
    }

    public ASTNode copy() {
        return new AtMost(getChild(0), getChild(1), getChild(2));
    }

    public boolean typecheck(SymbolTable st) {
        for (int i =0; i < 3; i++) {
            if (!getChild(i).typecheck(st)) {
                return false;
            }
            if (getChild(i).getDimension() != 1) {
                CmdFlags.println("ERROR: Expected one-dimensional matrix for each argument of atmost constraint: " + this);
                return false;
            }
        }
        if (getChild(1).getCategory() > ASTNode.Quantifier || getChild(2).getCategory() > ASTNode.Quantifier) {
            CmdFlags.println("ERROR: Atmost functions do not allow decision variables in the second or third arguments: " + this);
            return false;
        }
        if( (getChild(1) instanceof CompoundMatrix || getChild(1) instanceof EmptyMatrix) &&
            (getChild(2) instanceof CompoundMatrix || getChild(2) instanceof EmptyMatrix) )
        {
            if(getChild(1).numChildren() != getChild(2).numChildren()) {
                CmdFlags.println("ERROR: Atmost function expects second and third arguments to be the same length: " + this);
                return false;
            }
        }
        return true;
    }
    public ASTNode simplify() {
        ASTNode target=getChildConst(0);
        ASTNode occs=getChildConst(1);
        ASTNode values=getChildConst(2);
        
        if (occs instanceof EmptyMatrix) {
            assert values instanceof EmptyMatrix;
            // There are no value occurrence restrictions.
            return new BooleanConstant(true);
        }
        
        // Filter out occurrences that are n or more.
        if (target instanceof CompoundMatrix && occs instanceof CompoundMatrix && values instanceof CompoundMatrix) {
            for (int i =1; i < occs.numChildren(); i++) {
                if (occs.getChild(i).isConstant()) {
                    if(occs.getChild(i).getValue() >= target.numChildren() - 1) {
                        ArrayList<ASTNode> c1 = occs.getChildren(1);
                        c1.remove(i-1);
                        for(int j=0; j<c1.size(); j++) c1.get(j).setParent(null);
                        
                        ArrayList<ASTNode> c2 = values.getChildren(1);
                        c2.remove(i-1);
                        for(int j=0; j<c2.size(); j++) c2.get(j).setParent(null);
                        
                        getChild(0).setParent(null);
                        return new AtMost(getChild(0), CompoundMatrix.make(c1), CompoundMatrix.make(c2));
                    }
                    else if(occs.getChild(i).getValue() <= -1) {
                        // At most -1 occs of a value is impossible.
                        return new BooleanConstant(false);
                    }
                }
            }
        }
        
        // Now occurrence list is non-empty and no entries are greater than the upper limit
        
        // Case where target list is empty.
        if (target instanceof EmptyMatrix && (occs instanceof CompoundMatrix || occs instanceof EmptyMatrix)) {
            // Replace AtMost with constraints to say each card expression is >=0
            ArrayList<ASTNode> conjunction=new ArrayList<ASTNode>();
            for (int i =1; i < occs.numChildren(); i++) {
                if(occs == getChild(1)) {  //  Do not vandalise CMs in cmstore.
                    occs.getChild(i).setParent(null);
                }
                conjunction.add(new LessEqual(NumberConstant.make(0), occs.getChild(i)));
            }
            return new And(conjunction);
        }

        if (target instanceof CompoundMatrix && occs.getCategory() == ASTNode.Constant && values.getCategory() == ASTNode.Constant) {
            ArrayList<ASTNode> a = target.getChildren(1);
            
            ArrayList<ASTNode> occurs = occs.getChildren(1);
            
            //  For each element of a, take it out if it is a constant. 
            boolean isChanged=false;
            for (int i=a.size()-1; i >= 0; i--) {
                if (a.get(i).isConstant()) {
                    for(int j=0; j<values.numChildren()-1; j++) {
                        if(values.getChild(j+1).equals(a.get(i))) {
                            occurs.set(j, BinOp.makeBinOp("-", occurs.get(j), NumberConstant.make(1)));
                        }
                    }
                    
                    a.remove(i);
                    isChanged=true;
                }
            }
            
            if(isChanged) {
                getChild(2).setParent(null);
                if(target==getChild(0)) {
                    for(int j=0; j<a.size(); j++) a.get(j).setParent(null);
                }
                if(occs==getChild(1)) {
                    for(int j=0; j<occurs.size(); j++) occurs.get(j).setParent(null);
                }
                return new AtMost(CompoundMatrix.make(a), CompoundMatrix.make(occurs), getChild(2));
            }
        }
        return null;
    }
    public ASTNode normalise() {
        if (!(getChild(0) instanceof CompoundMatrix)) {
            return this;
        }

        // sort by hashcode
        ArrayList<ASTNode> ch = getChild(0).getChildren(1);
        boolean changed = sortByHashcode(ch);
        // ch cannot be empty.
        if (changed) {
            for(int i=0; i<ch.size(); i++) ch.get(i).setParent(null);
            getChild(1).setParent(null);
            getChild(2).setParent(null);
            return new AtMost(new CompoundMatrix(ch), getChild(1), getChild(2));
        } else {
            return this;
        }
    }
    
    public ASTNode normaliseAlpha() {
        if (!(getChild(0) instanceof CompoundMatrix)) {
            return null;
        }

        // sort by hashcode
        ArrayList<ASTNode> ch = getChild(0).getChildren(1);
        boolean changed = sortByAlpha(ch);
        // ch cannot be empty.
        if (changed) {
            for(int i=0; i<ch.size(); i++) ch.get(i).setParent(null);
            getChild(1).setParent(null);
            getChild(2).setParent(null);
            return new AtMost(new CompoundMatrix(ch), getChild(1), getChild(2));
        } else {
            return null;
        }
    }

    public boolean isRelation() { return true; }
    public boolean strongProp() {
        return false;   //  Decomposes to occurrenceleq
    }

    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
        assert getChild(2).getCategory() == ASTNode.Constant;
        assert bool_context;
        assert getChild(1) instanceof CompoundMatrix && getChild(1).numChildren() == 2;
        assert getChild(2) instanceof CompoundMatrix && getChild(2).numChildren() == 2;
        b.append("occurrenceleq(");
        getChild(0).toMinion(b, false);
        b.append(", ");
        getChild(2).getChild(1).toMinion(b, false);
        b.append(", ");
        getChild(1).getChild(1).toMinion(b, false);
        b.append(")");
    }
    public void toDominionInner(StringBuilder b, boolean bool_context) {
        assert getChild(2).getCategory() == ASTNode.Constant;
        b.append(CmdFlags.getCtName() + " ");
        b.append("occurrenceleq(flatten(");
        getChild(0).toDominion(b, false);
        b.append("), ");
        getChild(2).getChild(1).toDominion(b, false);
        b.append(", ");
        getChild(1).getChild(1).toDominion(b, false);
        b.append(")");
    }
    public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
        b.append("constraint at_most_int(");
        getChild(1).getChild(1).toFlatzinc(b, false);
        b.append(", ");
        getChild(0).toFlatzinc(b, false);
        b.append(", ");
        getChild(2).getChild(1).toFlatzinc(b, false);
        b.append(");");
    }
    public String toString() {
        return "atmost(" + getChild(0) + "," + getChild(1) + "," + getChild(2) + ")";
    }
    public void toMinizinc(StringBuilder b, boolean bool_context) {
        b.append("at_most(");
        getChild(1).getChild(1).toMinizinc(b, false);
        b.append(",");
        getChild(0).toMinizinc(b, false);
        b.append(",");
        getChild(2).getChild(1).toMinizinc(b, false);
        b.append(")");
    }

    public void toJSON(StringBuilder bf) {
        GlobalCard.toAlternateJSON(this, bf);
    }

    public boolean isChildSymmetric(int childIndex) {
        return childIndex == 0;
    }

}
