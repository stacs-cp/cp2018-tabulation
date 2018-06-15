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
import savilerow.treetransformer.*;

// Flatten a matrix to a one-dimensional matrix.

public class Flatten extends Unary
{
    public static final long serialVersionUID = 1L;
    public Flatten(ASTNode a) {
        super(a);
    }
    
    public ASTNode copy()
    {
        return new Flatten(getChild(0));
    }
    
    public boolean typecheck(SymbolTable st) {
        if(! getChild(0).typecheck(st)) return false;
        if(getChild(0).getDimension()<1) {
            System.out.println("ERROR: Expected matrix inside flatten function: "+this);
            return false;
        }
        return true;
	}
    
    public ASTNode simplify()
    {
        // Flatten is idempotent
        if(getChild(0) instanceof Flatten) {
            getChild(0).setParent(null);
            return getChild(0);
        }
        ASTNode mat=getChildConst(0);
        
        if(mat instanceof CompoundMatrix) {
            // Flatten of non-empty CM cannot be empty
            ArrayList<ASTNode> entries=flatten_compound_matrix(mat);
            
            boolean flat=true;
            for(int i=0; i<entries.size(); i++) {
                if(entries.get(i).getDimension()>0) {
                    flat=false;
                    break;
                }
            }
            if(flat) {
                if(mat==getChild(0)) {
                    for(int i=0; i<entries.size(); i++) entries.get(i).setParent(null);  //  cannibalise the source matrix.
                }
                return CompoundMatrix.make(entries);
            }
            else {
                // Do all or nothing. 
                return null;
            }
        }
        
        if(mat instanceof EmptyMatrix) {
            // Flatten of an empty matrix is a similar empty matrix with one empty dimension, and same base domain.  
            ArrayList<ASTNode> idxdoms=new ArrayList<ASTNode>();
            idxdoms.add(new IntegerDomain(new EmptyRange()));
            return new EmptyMatrix(new MatrixDomain(mat.getChild(0).getChild(0), idxdoms));
        }
        return null;
    }
    
    private ArrayList<ASTNode> flatten_compound_matrix(ASTNode cm) {
        assert cm instanceof CompoundMatrix;
        ArrayList<ASTNode> ch=cm.getChildren(1);   //  No need to construct new ArrayList here.
        
        ArrayList<ASTNode> ch2=list();
        for(int i=0; i<ch.size(); i++) {
            if(ch.get(i) instanceof CompoundMatrix) {
                // flatten it recursively and include it in here.
                ArrayList<ASTNode> entries=flatten_compound_matrix(ch.get(i));
                ch2.addAll(entries);
            } 
            else if(ch.get(i) instanceof EmptyMatrix) {
                // Drop it. 
            }
            else {
                ch2.add(ch.get(i));
            }
        }
        return ch2;
    }
    
    public ArrayList<Long> getValueSet() {
	    return getChild(0).getValueSet();
	}
	public Intpair getBounds() {
	    return getChild(0).getBounds();
	}
	public PairASTNode getBoundsAST() {
	    return getChild(0).getBoundsAST();
	}
    
    public boolean toFlatten(boolean propagate) {return false;}
    
    public boolean isRelation() {
        return getChild(0).isRelation();
    }
    public boolean isNumerical() {
        return getChild(0).isNumerical();
    }
    
    public int getDimension() {
        return 1;
    }
    
    public ArrayList<ASTNode> getIndexDomains() {
        // Find the index domain sizes of the inner matrix.
        
        ArrayList<ASTNode> idxdoms=getChild(0).getIndexDomains();
        if(idxdoms==null) {
            return null;
        }
        
        long numelements=1L;
        
        for(int i=0; i<idxdoms.size(); i++) {
            ArrayList<Intpair> ranges=idxdoms.get(i).getIntervalSet();
            long rangeitems=0;
            for(int j=0; j<ranges.size(); j++) {
                if(! (ranges.get(j).isEmpty())) rangeitems+=ranges.get(j).upper-ranges.get(j).lower+1L;
            }
            numelements=numelements*rangeitems;
        }
        
        idxdoms.clear();
        idxdoms.add(new IntegerDomain(new Range(NumberConstant.make(1), NumberConstant.make(numelements))));
        
	    return idxdoms;
	}
    
    public void toDominionInner(StringBuilder b, boolean bool_context) {
        b.append("flatten(");
        getChild(0).toDominion(b, false);
        b.append(")");
    }
    
	public void toDominionParam(StringBuilder b) {
	    b.append("flatten(");
	    getChild(0).toDominionParam(b);
	    b.append(")");
	}
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
	    // Minion implicitly flattens.
	    assert !bool_context;
	    getChild(0).toMinion(b, false);
	}
	public String toString()
	{
	    return "flatten("+getChild(0)+")";
	}
}
