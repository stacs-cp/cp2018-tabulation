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

public class CompoundMatrix extends ASTNodeC {
    public static final long serialVersionUID = 1L;
    // One-dimensional matrix made up of expressions.
    // May be nested. Child 0 is an index.
    public CompoundMatrix(ASTNode idx, ArrayList<ASTNode> m) {
        super(idx, m.toArray(new ASTNode[m.size()]));
        assert idx != null;
        assert m.size() > 0;
    }
    
    public CompoundMatrix(ASTNode idx, ASTNode[] m) {
        super(idx, m);
        assert idx != null;
        assert m.length > 0;
    }
    
    // CTOR with default index range of 1..n
    public CompoundMatrix(ArrayList<ASTNode> m) {
        ASTNode idx = new IntegerDomainConcrete(1, m.size());   //new Range(NumberConstant.make(1), NumberConstant.make(m.size())));
        ArrayList<ASTNode> a = new ArrayList<ASTNode>();
        a.add(idx); a.addAll(m);
        setChildren(a);
        assert m.size() > 0;
    }
    
    //  CTOR for copying only, index is included in the given array.
    public CompoundMatrix(ASTNode[] idxAndContents) {
        super(idxAndContents);
        assert idxAndContents[0]!=null;
    }
    
    // factory method for flat compound matrices. If it has to make an EmptyMatrix,
    // it assumes 1-d
    public static ASTNode make(ASTNode idx, ArrayList<ASTNode> m, boolean isBooleanMatrix) {
        if (m.size() > 0) {
            return new CompoundMatrix(idx, m);
        } else {
            ArrayList<ASTNode> idxdoms = new ArrayList<ASTNode>();
            idxdoms.add(idx);
            ASTNode basedom = isBooleanMatrix ? new BooleanDomain(new EmptyRange()) : new IntegerDomain(new EmptyRange());
            return new EmptyMatrix(new MatrixDomain(basedom, idxdoms));
        }
    }

    public static ASTNode make(ArrayList<ASTNode> m) {
        // Assume type integer, assume indexed from 1.
        if (m.size() == 0) {
            return CompoundMatrix.make(new IntegerDomain(new EmptyRange()), m, false);
        } else {
            return CompoundMatrix.make(new IntegerDomain(new Range(NumberConstant.make(1), NumberConstant.make(m.size()))), m, false);
        }
    }
    
    // Just one entry in matrix.
    public static ASTNode make(ASTNode a) {
        // Assume type integer, assume indexed from 1.
        ArrayList<ASTNode> m=new ArrayList<ASTNode>();
        m.add(a);
        return new CompoundMatrix(m);
    }
    
    // Two entries in matrix.
    public static ASTNode make(ASTNode a, ASTNode b) {
        // Assume type integer, assume indexed from 1.
        ArrayList<ASTNode> m=new ArrayList<ASTNode>();
        m.add(a); m.add(b);
        return new CompoundMatrix(m);
    }
    
    public boolean isRelation() {
        // For this to be relational, each element must be relational. 
        boolean all=true;
        for(int i=1; i<numChildren(); i++) {
            if(!getChild(i).isRelation()) { 
                all=false;
                break;
            }
        }
        return all;
    }
    @Override public boolean strongProp() {
        for(int i=1; i<numChildren(); i++) {
            if(!getChild(i).strongProp()) { 
                return false;
            }
        }
        return true;
	}
	
    public boolean isNumerical() {
        // For this to be numerical, one element must be numerical. (Others may be bools that are cast to int) 
        boolean one=false;
        for(int i=1; i<numChildren(); i++) {
            if(getChild(i).isNumerical()) { 
                one=true;
                break;
            }
        }
        return one;
    }
    public boolean isSet() {
        // All elements must be sets
        for(int i=1; i<numChildren(); i++) {
            if(!getChild(i).isSet()) { 
                return false;
            }
        }
        return true;
    }
    
    public ASTNode copy() {
        //  Use the special single array constructor.
        return new CompoundMatrix(getChildrenArray());
    }
    
    public boolean toFlatten(boolean propagate) { return false; }
    
    //  Bounds on a matrix are defined as the bounds on all expressions inside the matrix. 
    public Intpair getBounds() {
        Intpair bnds=getChild(1).getBounds();
        for (int i=2; i < numChildren(); i++) {
            Intpair a=getChild(i).getBounds();
            if(a.lower<bnds.lower) bnds.lower=a.lower;
            if(a.upper>bnds.upper) bnds.upper=a.upper;
        }
        return bnds;
    }
    // Also not an expression type with numerical bounds!
    // Used for simplify e.g. a safeelement contained in an equals.
    public PairASTNode getBoundsAST() {
        ArrayList<ASTNode> mins = new ArrayList<ASTNode>();
        ArrayList<ASTNode> maxs = new ArrayList<ASTNode>();
        for (int i=1; i < numChildren(); i++) {
            PairASTNode a = getChild(i).getBoundsAST();
            mins.add(a.e1);
            maxs.add(a.e2);
        }
        return new PairASTNode(new Min(mins), new Max(maxs));
    }
    public ArrayList<Intpair> getIntervalSetExp() {
        ArrayList<Intpair> bnds=getChild(1).getIntervalSetExp();
        for (int i=2; i < numChildren(); i++) {
            ArrayList<Intpair> a=getChild(i).getIntervalSetExp();
            bnds=Intpair.union(bnds, a);
        }
        return bnds;
    }
    
    @Override
    public boolean typecheck(SymbolTable st) {
        for(int i=0; i<numChildren(); i++) {
            if(!getChild(i).typecheck(st)) return false; 
        }
        
        // Must have uniform dimension.
        int dim=getChild(1).getDimension();
        for(int i=2; i<numChildren(); i++) {
            if(getChild(i).getDimension()!=dim) {
                System.out.println("ERROR: In matrix literal: "+this); 
                System.out.println("ERROR: Elements in matrix literal have different numbers of dimensions.");
                return false;
            }
        }
        
        if(!getChild(0).isFiniteSet()) {
            System.out.println("ERROR: In matrix literal: "+this); 
            System.out.println("ERROR: Index set is not a finite set.");
            return false;
        }
        
        // Is the index set the right size?
        
        
        //  Not yet checking distinction between set and int/bool.
        
	    return true;
	}
    
    // Assumes the dimension is the same everywhere.
    public int getDimension() {
        if (numChildren() == 1) {
            assert false : "CompoundMatrix type must have non-zero size.";
            return 1;
        }
        else {
            return 1 + getChild(1).getDimension();
        }
    }
    
    // For a matrix literal, is it regular?
    @Override
    public boolean isRegularMatrix() {
        if(getDimension()>1) {
            //  First check all matrices contained in here are individually regular
            for(int i=1; i<numChildren(); i++) {
                if(! getChild(i).isRegularMatrix()) {
                    return false;
                }
            }
            
            // Second, check all matrices contained within here have the same index domains.
            // Should be in a unique normal form following simplification. Relies on simplifier of IntegerDomain.
            ArrayList<ASTNode> idx1=getChild(1).getIndexDomains();
            
            for(int i=2; i<numChildren(); i++) {
                if(! getChild(i).getIndexDomains().equals(idx1)) {
                    return false;
                }
            }
        }
        
        // If 1-dimensional, then must be regular. 
        return true;
    }
    
    // For a regular matrix literal only, get the index domains.
    public ArrayList<ASTNode> getIndexDomains() {
        ArrayList<ASTNode> tmp;
        assert numChildren() >= 2;
        if(getDimension()>1) {
            tmp = getChild(1).getIndexDomains();
            if(tmp==null) {
                //  First child cannot tell us its index yet.
                return null;
            }
        }
        else {
            // One-dimensional.
            tmp = new ArrayList<ASTNode>();
        }
        tmp.add(0, getChild(0));   //  Add index of this.
        return tmp;
    }
    
    // Much slower version for irregular matrices.
    public ArrayList<ASTNode> getIndexDomainsIrregular() {
        ArrayList<ASTNode> out=new ArrayList<ASTNode>();
        
        out.add(getChild(0));
        
        if(getDimension()>1) {
            for(int i=1; i<numChildren(); i++) {
                ArrayList<ASTNode> tmp=getChild(i).getIndexDomainsIrregular();
                
                if(i==1) {
                    out.addAll(tmp);
                }
                else {
                    // Check if tmp differs from out anywhere. If so, that would be an irregular dimension.
                    //  Assumes that two domains are symbolically equal if they contain the same set of values.
                    for(int j=1; j<out.size(); j++) {
                        if(! (tmp.get(j-1).equals(out.get(j)))) {
                            out.set(j, new IntegerDomain(new Range(null, null)));
                        }
                    }
                }
            }
        }
        
        return out;
    }
    
    @Override public boolean isMatrixLiteral() {
        if(getDimension()>1) {
            //  Check children have literal structure as well.
            for(int i=1; i<numChildren(); i++) {
                if(!getChild(i).isMatrixLiteral()) {
                    return false;
                }
            }
        }
        return true;
    }
    
    // ALL output methods except E' drop the index.
    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
        assert !bool_context;
        b.append("[");
        for (int i =1; i < numChildren(); i++) {
            getChild(i).toMinion(b, false);
            if (i < numChildren() - 1) {
                b.append(", ");
            }
        }
        b.append("]");
    }
    public void toDominionInner(StringBuilder b, boolean bool_context) {
        b.append("[");
        for (int i =1; i < numChildren(); i++) {
            getChild(i).toDominion(b, false);
            if (i < numChildren() - 1) {
                b.append(", ");
            }
        }
        b.append("]");
    }
    public void toDominionParam(StringBuilder b) {
        b.append("[");
        for (int i =1; i < numChildren(); i++) {
            getChild(i).toDominionParam(b);
            if (i < numChildren() - 1) {
                b.append(", ");
            }
        }
        b.append("]");
    }

    public String toString() {
        StringBuilder st = new StringBuilder();
        st.append("[");
        for (int i =1; i < numChildren(); i++) {
            st.append(getChild(i).toString());

            if (i < numChildren() - 1) {
                st.append(", ");
                if (getChild(i) instanceof CompoundMatrix || getChild(i) instanceof EmptyMatrix) {
                    st.append("\n");
                }
            }
        }
        //  Don't output index domains of the form int(1..10) or int(1), i.e. the default indexing. 
        ArrayList<Intpair> p=getChild(0).getIntervalSet();
        if(p==null || p.size()!=1 || p.get(0).lower!=1) {
            st.append(";");
            st.append(getChild(0).toString());
        }
        
        st.append("]");
        return st.toString();
    }
    
    public String toStringSimpleMatrix() {
        StringBuilder st = new StringBuilder();
        st.append("[");
        for (int i =1; i < numChildren(); i++) {
            if(getChild(i) instanceof CompoundMatrix) {
                st.append(((CompoundMatrix)getChild(i)).toStringSimpleMatrix());
            }
            else if(getChild(i) instanceof EmptyMatrix) {
                st.append("[ ]");
            }
            else {
                st.append(getChild(i).toString());
            }
            
            if (i < numChildren() - 1) {
                st.append(", ");
                if (getChild(i) instanceof CompoundMatrix || getChild(i) instanceof EmptyMatrix) {
                    st.append("\n");
                }
            }
        }
        st.append("]");
        return st.toString();
    }

    public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
        b.append("[");
        for (int i =1; i < numChildren(); i++) {
            getChild(i).toFlatzinc(b, bool_context);
            if (i < numChildren() - 1) {
                b.append(", ");
            }
        }
        b.append("]");
    }

    public void toMinizinc(StringBuilder b, boolean bool_context) {
        b.append("[");
        for (int i =1; i < numChildren(); i++) {
            getChild(i).toMinizinc(b, bool_context);
            if (i < numChildren() - 1) {
                b.append(", ");
            }
        }
        b.append("]");
    }

    public void toJSON(StringBuilder bf) {
        toJSONHeader(bf, true);
        // children
        bf.append("\"Domain\":");
        getChild(0).toJSON(bf);
        bf.append(",\n");
        bf.append("\"Children\": [");
        int numberChildren = numChildren();
        // skip first child as this is domain
        for (int i = 1; i < numChildren(); i++) {
            bf.append("\n");
            getChild(i).toJSON(bf);
            // not last child
            if (i < numberChildren - 1) {
                bf.append(",");
            }
        }
        bf.append("]\n}");
    }

    public boolean childrenAreSymmetric() {
        return getParent().isChildSymmetric(getChildNo());
    }
}
