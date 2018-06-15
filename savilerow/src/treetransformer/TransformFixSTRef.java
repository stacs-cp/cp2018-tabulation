package savilerow.treetransformer;
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


import savilerow.expression.*;
import savilerow.model.*;

import java.util.*;

public class TransformFixSTRef extends TreeTransformerBottomUpNoWrapper
{
    Model replace_m;
    public TransformFixSTRef(Model _replace_m) {
        super(null);
        replace_m=_replace_m;
    }
    
	protected NodeReplacement processNode(ASTNode curnode) {
	    if(curnode.hasModel()) {
	        curnode.setModel(replace_m);
	    }
	    return null;
	}
}
