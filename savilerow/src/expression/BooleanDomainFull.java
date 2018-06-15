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
// Represents domains of type boolean. The full Boolean type only. 

public class BooleanDomainFull extends SimpleDomain
{
    public static final long serialVersionUID = 1L;
    public BooleanDomainFull() {
        super();
    }
    public ArrayList<Long> getValueSet() {
        ArrayList<Long> tmp=new ArrayList<Long>(2);
        tmp.add(0L); tmp.add(1L);
        return tmp;
    }
    
    public ASTNode copy() {
	    return new BooleanDomainFull();
	}
	public Intpair getBounds() {
	    return new Intpair(0L, 1L);
	}
	public PairASTNode getBoundsAST() {
	    return new PairASTNode(NumberConstant.make(0), NumberConstant.make(1));
	}
	
	public ArrayList<Intpair> getIntervalSet() {
	    ArrayList<Intpair> tmp=new ArrayList<Intpair>();
	    tmp.add(getBounds());
	    return tmp;
	}
	
	public boolean containsValue(long val) {
	    return val>=0L && val<=1L;
	}
	
	@Override
	public boolean isBooleanSet() {
	    return true;
	}
	
	@Override
    public boolean isFiniteSet() {
        return true;
    }
    @Override
    public boolean isFiniteSetUpper() {
        return true;
    }
    @Override
    public boolean isFiniteSetLower() {
        return true;
    }
	
	public String toString() {
	    return "bool";
	}
}
