package savilerow.model;
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

import savilerow.CmdFlags;
import savilerow.expression.*;
import savilerow.treetransformer.*;
import savilerow.*;

import java.util.*;
import java.lang.Math;
import java.io.*;

// Very straightforward implementation of a symbol table that maps
// variables (looked up by name) to their domain and category (parameter or decision)
// Quantifier variables are not included here, only global ones.

public class SymbolTable implements Serializable {
    private static final long serialVersionUID = 1L;
    
    public transient Model m;
    
    public ArrayDeque<ASTNode> lettings_givens;    // Lettings, givens, wheres, finds in order.
    
    // Category has an entry for each symbol.
    public HashMap<String, categoryentry> category;
    
    public categoryentry category_first;
    public categoryentry category_last;
    
    // Arraylist version of the above for serialization.
    private ArrayList<categoryentry> category_list;
    
    // domains and constant_matrices have entries whenever the symbol has an
    // associated domain and/or constant matrix
    
    // Domain could be an identifier -- should be defined in a  letting.
    private HashMap<String, ASTNode> domains;
    
    public transient HashMap<String, String> represents_ct;    // String representation of the ct the aux var represents.
    
    // Yet another data structure -- for matrices that have been replaced with
    // atomic variables. 
    public HashMap<String, ASTNode> deleted_matrices;
    
    public HashMap<String, replaces_matrix_entry> replaces_matrix;    // as in replaces["M___5___4"]=<"M", [5,4]>
    
    int auxvarcounter;
    
    public HashMap<ASTNode, ASTNode> replacements;    // Variables that have been deleted and replaced with either
    // another variable, a constant or a simple expression like a negation of a variable. 
    public HashMap<ASTNode, ASTNode> replacements_domains;    // Domains for deleted vars at the point of deletion.
    public HashMap<ASTNode, Integer> replacements_category;    // Category of deleted vars at point of deletion.
    
    //  Special hash-tables for marking variables as bool, int or both. 
    HashMap<String, Boolean> boolvar_bool;    // Not included in .equals comparison or copy.
    HashMap<String, Boolean> boolvar_int;
    
    //   When encoding to SAT, some variables marked as needing direct encoding. 
    HashSet<String> directvar_sat;
    
    public SymbolTable() {
        lettings_givens = new ArrayDeque<ASTNode>();
        domains = new HashMap<String, ASTNode>();

        // This is the ordering on the symbols for output.
        category = new HashMap<String, categoryentry>();
        category_first = null;
        category_last = null;

        represents_ct = new HashMap<String, String>();
        auxvarcounter = 0;

        // Extra data for gecode and minizinc output.
        boolvar_bool = new HashMap<String, Boolean>();
        boolvar_int = new HashMap<String, Boolean>();

        deleted_matrices = new HashMap<String, ASTNode>();
        replaces_matrix = new HashMap<String, replaces_matrix_entry>();

        replacements = new HashMap<ASTNode, ASTNode>();
        replacements_domains = new HashMap<ASTNode, ASTNode>();
        replacements_category = new HashMap<ASTNode, Integer>();
    }
    
    private void category_put_end(String name, int cat) {
        if (category_last == null) {
            assert category_first == null;
            category_first = category_last = new categoryentry(name, cat, null, null);
        } else {
            categoryentry tmp = new categoryentry(name, cat, category_last, null);
            category_last.next = tmp;
            category_last = tmp;
        }
        category.put(name, category_last);
    }
    
    @Override
    public boolean equals(Object b) {
        if (! (b instanceof SymbolTable)) {
            return false;
        }
        SymbolTable c = (SymbolTable) b;
        
        // Omitting m.
        
        // Irritatingly ArrayDeque does not have its own .equals.
        if(! Arrays.equals(lettings_givens.toArray(), c.lettings_givens.toArray())) {
            return false;
        }
        
        if (! c.category.equals(category)) {
            return false;
        }
        // Iterate down the categoryentry list checking equality. Can't do this recursively because it blows the stack.
        categoryentry iter_this = category_first;
        categoryentry iter_other = c.category_first;
        while (iter_this != null || iter_other != null) {
            if (iter_this == null || iter_other == null) {
                // One is null and the other is not.
                return false;
            }

            if (! iter_this.equals(iter_other)) {
                return false;
            }

            assert iter_this.next == null || iter_this.next.prev == iter_this;
            assert iter_other.next == null || iter_other.next.prev == iter_other;
            assert iter_this.next != null || iter_this == category_last;
            assert iter_other.next != null || iter_other == c.category_last;

            iter_this = iter_this.next;
            iter_other = iter_other.next;
        }

        if (! c.domains.equals(domains)) {
            return false;
        }
        
        if (! c.represents_ct.equals(represents_ct)) {
            return false;
        }
        
        if (! c.deleted_matrices.equals(deleted_matrices)) {
            return false;
        }
        if (! c.replaces_matrix.equals(replaces_matrix)) {
            return false;
        }
        if (c.auxvarcounter != auxvarcounter) {
            return false;
        }

        if (! c.replacements.equals(replacements)) {
            return false;
        }
        if (! c.replacements_domains.equals(replacements_domains)) {
            return false;
        }
        if (! c.replacements_category.equals(replacements_category)) {
            return false;
        }

        return true;
    }
    
    @Override public int hashCode() {
        // The linked list  -- generate a hash that depends on the order of variable names. 
        int hashlist=0;
        categoryentry iter = category_first;
        while (iter != null) {
            hashlist=(6091*hashlist) + (iter.name.hashCode());
            iter=iter.next;
        }
        
        return Objects.hash(Arrays.hashCode(lettings_givens.toArray()), category, 
            hashlist, domains, represents_ct, deleted_matrices, replaces_matrix, 
            auxvarcounter, replacements, replacements_domains, replacements_category);
    }
    
    public SymbolTable copy(Model new_m) {
        SymbolTable st = new SymbolTable();
        st.m=new_m;
        TransformFixSTRef tf = new TransformFixSTRef(new_m);
        
        // Copy lettings, givens etc in sequence.
        for (Iterator<ASTNode> itr = lettings_givens.iterator(); itr.hasNext();) {
            ASTNode letgiv = itr.next();
            st.lettings_givens.addLast(tf.transform(letgiv.copy()));
        }
        
        categoryentry cur = category_first;
        while (cur != null) {
            st.category_put_end(cur.name, cur.cat);
            cur = cur.next;
        }
        
        for (String domst : domains.keySet()) {
            st.domains.put(domst, tf.transform(domains.get(domst).copy()));
        }
        
        st.represents_ct = new HashMap<String, String>(represents_ct);
        for (String delst : deleted_matrices.keySet()) {
            st.deleted_matrices.put(delst, tf.transform(deleted_matrices.get(delst).copy()));
        }
        for (String repmat : replaces_matrix.keySet()) {
            replaces_matrix_entry r1 = new replaces_matrix_entry(replaces_matrix.get(repmat).name, new ArrayList<Long>(replaces_matrix.get(repmat).idx));
            st.replaces_matrix.put(repmat, r1);
        }
        st.auxvarcounter = auxvarcounter;
        
        for (ASTNode rep1 : replacements.keySet()) {
            st.replacements.put(tf.transform(rep1.copy()), tf.transform(replacements.get(rep1).copy()));
        }
        for (ASTNode rep2 : replacements_domains.keySet()) {
            st.replacements_domains.put(tf.transform(rep2.copy()), tf.transform(replacements_domains.get(rep2).copy()));
        }
        for (ASTNode rep3 : replacements_category.keySet()) {
            st.replacements_category.put(tf.transform(rep3.copy()), (int) replacements_category.get(rep3));
        }
        
        return st;
    }
    
    // To add parameters
    public void newVariable(String name, ASTNode dom, int cat) {
        assert ! category.containsKey(name);
        domains.put(name, dom);
        category_put_end(name, cat);
    }
    
    // To add variables replacing a matrix
    public void newVariable(String name, ASTNode dom, int cat, ASTNode replaces, ArrayList<Long> indices) {
        assert ! category.containsKey(name);
        domains.put(name, dom);
        if (dom.getCategory() == ASTNode.Constant) {
            ArrayList<Intpair> set = dom.getIntervalSet();
            if (set.size() == 0) {
                CmdFlags.println("ERROR: Empty domain");
            }
        }
        categoryentry c = category.get(replaces.toString());        // Add directly before this

        categoryentry newcat = new categoryentry(name, cat, c.prev, c);

        // stitch it in
        if (newcat.next == null) {
            category_last = newcat;
        } else {
            newcat.next.prev = newcat;
        }
        if (newcat.prev == null) {
            category_first = newcat;
        } else {
            newcat.prev.next = newcat;
        }

        category.put(name, newcat);

        replaces_matrix.put(name, new replaces_matrix_entry(replaces.toString(), new ArrayList<Long>(indices)));
    }

    //////////////////////////////////////////////////////////////////////////// 
    // Unify two equal decision variables.
    
    public void unifyVariables(ASTNode id1, ASTNode id2) {
        assert id1.getCategory() == ASTNode.Decision && id2.getCategory() == ASTNode.Decision;
        
        // If one is an aux var and the other isn't, the aux var will be deleted.
        // If one has the prefix "incumbent_" generated by Conjure for SNS incumbent variables,
        // the incumbent variable will be deleted. 
        if (category.get(id1.toString()).cat == ASTNode.Auxiliary 
            || (id1.toString().length()>=10 && id1.toString().substring(0,10).equals("incumbent_")) ) {
            // Swap.
            ASTNode temp = id1;
            id1 = id2;
            id2 = temp;
        }
        // There is always a branchingon list, so it doesn't matter which one is eliminated.
        
        TransformSimplify ts = new TransformSimplify();
        
        ASTNode intersectDomain=new Intersect(getDomain(id1.toString()), getDomain(id2.toString()));
        
        // Intersect correctly casts a boolean set to a non-boolean set when
        // intersecting it with a set of int. Sort out the boolean case.
        // This is a rather unpleasant hack.
        if(getDomain(id1.toString()).isBooleanSet()) {
            intersectDomain = Intpair.makeDomain((ts.transform(intersectDomain)).getIntervalSet(), true);
        }
        intersectDomain=ts.transform(intersectDomain);
        
        setDomain(id1.toString(), intersectDomain);
        
        // id2 will be replaced by id1.
        replacements.put(id2, id1);
        // this hash table will be used to find its value.
        replacements_domains.put(id2, getDomain(id2.toString()));
        replacements_category.put(id2, category.get(id2.toString()).cat);
        
        // Delete id2 in Symboltable.
        deleteSymbol(id2.toString());
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //   Unify two decision variables when one is the negation of the other.
    
    public void unifyVariablesNegated(ASTNode id1, ASTNode id2) {
        assert id1.getCategory() == ASTNode.Decision && id2.getCategory() == ASTNode.Decision;
        assert id2 instanceof Negate;
        id2=id2.getChild(0);  // Strip off the negation.
        
        assert id1.isRelation() && id2.isRelation();
        
        // If one is an aux var and the other isn't, the aux var should be deleted.
        if (category.get(id1.toString()).cat == ASTNode.Auxiliary) {
            // Swap.
            ASTNode temp = id1;
            id1 = id2;
            id2 = temp;
        }
        
        // If there is a branchingon list (and now there always is), it doesn't matter which one is eliminated.
        
        TransformSimplify ts = new TransformSimplify();
        
        // In some strange cases one or other might be assigned or empty, so intersect the domains. 
        setDomain(id1.toString(), ts.transform(new Intersect(getDomain(id1.toString()), getDomain(id2.toString()))));
        
        // id2 will be replaced by not id1.
        replacements.put(id2, new Negate(id1));
        // this hash table will be used to find its value.
        replacements_domains.put(id2, getDomain(id2.toString()));
        replacements_category.put(id2, category.get(id2.toString()).cat);
        
        // get rid of id2 in Symboltable. Don't need to worry about
        // branchingon or other places because it will be done using ReplaceASTNode.
        deleteSymbol(id2.toString());
    }
    
    //////////////////////////////////////////////////////////////////////////// 
    // 
    // Delete variable when it is assigned.

    public void assignVariable(ASTNode id, ASTNode value) {
        assert (!CmdFlags.getUseAggregate()) || CmdFlags.getAfterAggregate();
        assert id instanceof Identifier;
        assert value.isConstant();
        assert getDomain(id.toString()).containsValue(value.getValue());
        assert id.getModel().global_symbols==this;
        
        if(id.isRelation() && !value.isRelation()) {
            long v=value.getValue();
            assert v>=0 && v<=1;
            value=new BooleanConstant(v==1);
        }
        
        //System.out.println("Assign "+id+", "+value+" with domains "+getDomain(id.toString()));
        
        replacements.put(id, value);        // This will be used to retrieve the value when parsing solver output.
        replacements_domains.put(id, getDomain(id.toString()));
        replacements_category.put(id, category.get(id.toString()).cat);
        
        deleteSymbol(id.toString());
        
        if(m.sns != null && CmdFlags.getMinionSNStrans()) {
            ASTNode primaries=m.sns.getChild(0).getChild(0);
            ASTNode incumbents=m.sns.getChild(0).getChild(1);
            
            ///  Horrifying cost of n just to assign a variable when using SNS.
            for(int i=1; i<primaries.numChildren(); i++) {
                if(primaries.getChild(i).equals(id)) {
                    ASTNode incumbent=incumbents.getChild(i);
                    
                    if(getDomain(incumbent.toString())!=null) {
                        //  If incumbent has not already been deleted, by having a single value in domain...
                        assignVariable(incumbent, value.copy());
                    }
                    break;
                }
            }
        }
    }
    
    public ASTNode getDomain(String varid) {
        return domains.get(varid);
    }
    
    public void setDomain(String varid, ASTNode d) {
        domains.put(varid, d);
    }
    
    public boolean isAuxiliary(String varid) {
        return category.get(varid).cat==ASTNode.Auxiliary;
    }
    
    public HashMap<String, ASTNode> getDomains() { return domains; }
    
    public categoryentry getCategoryFirst() { return category_first; }
    
    public int getCategory(String varid) {
        if (category.get(varid) == null) {
            return ASTNode.Undeclared;
        }
        int i = category.get(varid).cat;
        if (i == ASTNode.Auxiliary) {
            return ASTNode.Decision;
        }
        if (i == ASTNode.ConstantMatrix) {
            return ASTNode.Constant;
        }
        return i;
    }
    
    public boolean hasVariable(String varid) {
        return category.containsKey(varid);
    }
    
    //  Find unused name for new auxiliary id.
    public String newAuxId() {
        String newname = "aux" + auxvarcounter;
        while (category.containsKey(newname)) {
            auxvarcounter++;
            newname = "aux" + auxvarcounter;
        }
        auxvarcounter++;
        return newname;
    }
    
    public Identifier newAuxiliaryVariable(long lb, long ub) {
        String newname = newAuxId();
        if (lb != 0 || ub != 1) {
            domains.put(newname, new IntegerDomain(new Range(NumberConstant.make(lb), NumberConstant.make(ub))));
        } else {
            domains.put(newname, new BooleanDomainFull());
        }
        
        category_put_end(newname, ASTNode.Auxiliary);
        return new Identifier(m, newname);
    }
    
    public Identifier newAuxiliaryVariable(ASTNode dom) {
        String newname = newAuxId();
        
        //  Convert from 0..1 to boolean as in the method above. 
        ArrayList<Intpair> a=dom.getIntervalSet();
        if(a.size()==1 && a.get(0).lower==0 && a.get(0).upper==1) {
            domains.put(newname, new BooleanDomainFull());
        }
        else {
            domains.put(newname, dom.copy());
        }
        
        category_put_end(newname, ASTNode.Auxiliary);
        return new Identifier(m, newname);
    }
    
    // newAuxHelper just takes an expression and makes an auxiliary variable for it.
    // Deals with FilteredDomainStorage. 
    public ASTNode newAuxHelper(ASTNode exp) {
        ArrayList<Intpair> a=exp.getIntervalSetExp();
        ASTNode auxdom=Intpair.makeDomain(a, exp.isRelation());
        auxdom=m.filt.constructDomain(exp, auxdom);  //  Look up stored (filtered) domain if there is one.
        
        ASTNode auxvar=newAuxiliaryVariable(auxdom);
        m.filt.auxVarRepresentsAST(auxvar.toString(), exp);    //  Associate the expression to the variable in FilteredDomainStorage
        return auxvar;
    }
    
    // newAuxHelper just takes an expression and makes an auxiliary variable for it.
    // Deals with FilteredDomainStorage. 
    public ASTNode newAuxHelper(ASTNode exp, ASTNode maxdomain) {
        ArrayList<Intpair> a=exp.getIntervalSetExp();
        ASTNode ints=new Intersect(Intpair.makeDomain(a, exp.isRelation()), maxdomain);
        ASTNode auxdom=m.filt.constructDomain(exp, ints);  //  Look up stored (filtered) domain if there is one.
        auxdom=(new TransformSimplify()).transform(auxdom);
        ASTNode auxvar=newAuxiliaryVariable(auxdom);
        m.filt.auxVarRepresentsAST(auxvar.toString(), exp);    //  Associate the expression to the variable in FilteredDomainStorage
        return auxvar;
    }
    
    //  Used exclusively by class-level flattening.
    public Identifier newAuxiliaryVariable(ASTNode lb, ASTNode ub) {
        String newname = newAuxId();
        domains.put(newname, new IntegerDomain(new Range(lb, ub)));
        category_put_end(newname, ASTNode.Auxiliary);
        return new Identifier(m, newname);
    }
    
    //  Create matrix of aux variables. Also used exclusively by class-level flattening.
    public Identifier newAuxiliaryVariableMatrix(ASTNode lb, ASTNode ub, ArrayList<ASTNode> q_id, ArrayList<ASTNode> qdoms, ArrayList<ASTNode> conditions) {
        // Class-level flattening requires sausage matrix.
        String newname = newAuxId();
        category_put_end(newname, ASTNode.Auxiliary);

        // indexed by the quantifier domains.
        domains.put(newname, new MatrixDomain( new IntegerDomain(new Range(lb, ub)), qdoms, new Container(q_id), new And(conditions)));

        return new Identifier(m, newname);
    }
    
    ////////////////////////////////////////////////////////////////////////////
    // 
    //  Constant matrices
    public void registerConstantMatrix(String name) {
        if (category.containsKey(name)) {            // Should be a parameter...
            assert category.get(name).cat == ASTNode.Parameter;
            // Make it a constant matrix
            category.get(name).cat = ASTNode.ConstantMatrix;
        } else {
            category_put_end(name, ASTNode.ConstantMatrix);
        }
    }
    
    
    
    
    // Add some info that is helpful for debugging
    public void auxVarRepresentsConstraint(String name, String ct) {
        represents_ct.put(name, ct.replaceAll("\n", ""));  // Get rid of any newlines that cause problems in comments.
    }

    public String toString() {
        StringBuilder b = new StringBuilder();
        categoryentry c = category_first;
        while (c != null) {
            String name = c.name;
            ASTNode dom = getDomain(name);
            
            if (getCategory(name) == ASTNode.Parameter) {
                b.append("given ");
            } else if (getCategory(name) == ASTNode.Decision) {
                b.append("find ");
            }
            
            b.append(name);
            b.append(" : ");
            b.append(dom.toString());
            b.append("\n");
            c = c.next;
        }
        return b.toString();
    }

    public boolean simplify() {
        // Simplify the expressions in the domains and matrices of constants.
        TransformSimplify ts = new TransformSimplify();
        
        ArrayList<String> delete_vars = new ArrayList<String>();

        // Simplify lettings_givens.
        int size = lettings_givens.size();
        for (int i =0; i < size; i++) {            // For each one, take it off the front and add back to the end of the deque.
            lettings_givens.addLast(ts.transform(lettings_givens.removeFirst()));
        }
        
        boolean emptyDomain=false;  // set true when we see an empty domain.
        Iterator<Map.Entry<String, ASTNode>> itr = domains.entrySet().iterator();
        while (itr.hasNext()) {
            Map.Entry<String, ASTNode> d = itr.next();
            
            ASTNode dom = d.getValue();
            // atl.transform(dom);
            dom = ts.transform(dom);
            d.setValue(dom);
            
            // Check for unit domains.  Sometimes arise after unifying two vars,
            // or might be given by the user.
            if (dom.getCategory() == ASTNode.Constant && dom.isFiniteSet()) {
                Intpair bnds = dom.getBounds();
                if(bnds.upper<bnds.lower) {
                    emptyDomain=true;
                }
                if (CmdFlags.getUseDeleteVars() && bnds.lower==bnds.upper) {
                    delete_vars.add(d.getKey());
                }
            }
        }
        
        // Now delete the unit variables.
        if (CmdFlags.getUseDeleteVars() && (!CmdFlags.getUseAggregate() || CmdFlags.getAfterAggregate())) {
            for (int i =0; i < delete_vars.size(); i++) {
                if(getDomain(delete_vars.get(i)) != null) {
                    ASTNode value = NumberConstant.make(getDomain(delete_vars.get(i)).getBounds().lower);  // assignVariable converts to bool if necessary
                    assignVariable(new Identifier(m, delete_vars.get(i)), value);
                }
            }
        }
        
        return !emptyDomain;
    }

    public void transform_all(TreeTransformer t) {
        // Poke into every corner and apply t.

        // do lettings_givens
        int size = lettings_givens.size();
        for (int i =0; i < size; i++) {            // For each one, take it off the front and add back to the end of the deque.
            lettings_givens.addLast(t.transform(lettings_givens.removeFirst()));
        }

        // Domains
        Iterator<Map.Entry<String, ASTNode>> itr = domains.entrySet().iterator();
        while (itr.hasNext()) {
            Map.Entry<String, ASTNode> d = itr.next();
            ASTNode dom = d.getValue();
            d.setValue(t.transform(dom));
        }

        itr = deleted_matrices.entrySet().iterator();
        while (itr.hasNext()) {
            Map.Entry<String, ASTNode> d = itr.next();
            ASTNode mat = d.getValue();
            d.setValue(t.transform(mat));
        }

        HashMap<ASTNode, ASTNode> newreplacements = new HashMap<ASTNode, ASTNode>();
        Iterator<Map.Entry<ASTNode, ASTNode>> itr2 = replacements.entrySet().iterator();
        while (itr2.hasNext()) {
            Map.Entry<ASTNode, ASTNode> d = itr2.next();
            ASTNode left = t.transform(d.getKey());
            ASTNode right = t.transform(d.getValue());
            newreplacements.put(left, right);
        }
        this.replacements = newreplacements;

        HashMap<ASTNode, ASTNode> newreplacements_domains = new HashMap<ASTNode, ASTNode>();
        itr2 = replacements_domains.entrySet().iterator();
        while (itr2.hasNext()) {
            Map.Entry<ASTNode, ASTNode> d = itr2.next();
            ASTNode left = t.transform(d.getKey());
            ASTNode right = t.transform(d.getValue());
            newreplacements_domains.put(left, right);
        }
        this.replacements_domains = newreplacements_domains;

        HashMap<ASTNode, Integer> newreplacements_category = new HashMap<ASTNode, Integer>();
        Iterator<Map.Entry<ASTNode, Integer>> itr3 = replacements_category.entrySet().iterator();
        while (itr3.hasNext()) {
            Map.Entry<ASTNode, Integer> d = itr3.next();
            ASTNode left = t.transform(d.getKey());
            newreplacements_category.put(left, (int) d.getValue());
        }
        this.replacements_category = newreplacements_category;
    }

    public void substitute(ASTNode toreplace, ASTNode replacement) {
        ReplaceASTNode t = new ReplaceASTNode(toreplace, replacement);

        Iterator<Map.Entry<String, ASTNode>> itr = domains.entrySet().iterator();
        while (itr.hasNext()) {
            Map.Entry<String, ASTNode> d = itr.next();
            ASTNode dom = d.getValue();

            d.setValue(t.transform(dom));
        }

        int size = lettings_givens.size();
        for (int i =0; i < size; i++) {            // For each one, take it off the front and add back to the end of the deque.
            ASTNode letgiv = lettings_givens.removeFirst();
            ASTNode firstchild = letgiv.getChild(0);            // Don't sub into the first child-- it's the identifier.
            letgiv = t.transform(letgiv);
            letgiv.setChild(0, firstchild);
            lettings_givens.addLast(letgiv);
        }
    }

    public boolean typecheck() {
        // At this point, lettings have been substituted in so all things in
        // 'domains' should be of type Domain.
        for (String a : domains.keySet()) {
            ASTNode d = domains.get(a);
            if (! (d instanceof Domain)) {
                CmdFlags.println("ERROR: Found " + d + " when expecting domain for symbol " + a);
                return false;
            }
            if (!d.typecheck(this)) {
                return false;
            }

            if (getCategory(a) == ASTNode.Decision) {
                // Do some extra checks for finiteness for decision variable matrices.
                if (d instanceof MatrixDomain) {
                    for (int i =3; i < d.numChildren(); i++) {
                        if(!(d.getChild(i) instanceof MatrixDomain) && !(d.getChild(i).isFiniteSet())) {
                            CmdFlags.println("ERROR: Found " + d.getChild(i) + " when expecting finite integer domain for indices of matrix variable " + a);
                            return false;
                        }
                    }
                    if (!(d.getChild(0).isFiniteSet())) {
                        CmdFlags.println("ERROR: Found " + d.getChild(0) + " when expecting finite integer domain for decision variable " + a);
                        return false;
                    }
                } else if (!(d.isFiniteSet())) {
                    CmdFlags.println("ERROR: Found " + d + " when expecting finite integer domain for decision variable " + a);
                    return false;
                }
            }
        }
        return true;
    }

    // Delete a symbol from the table for good.
    public void deleteSymbol(String name) {
        assert category.containsKey(name);
        categoryentry c = category.get(name);
        if (c.prev != null) {
            c.prev.next = c.next;
        } else {
            category_first = c.next;
        }
        if (c.next != null) {
            c.next.prev = c.prev;
        } else {
            category_last = c.prev;
        }
        category.remove(name);

        if (domains.containsKey(name)) {
            domains.remove(name);
        }
        if (m.cmstore.hasConstantMatrix(name)) {
            m.cmstore.removeConstantMatrix(name);
        }
    }

    public void deleteMatrix(String name) {
        // This symbol is a matrix of decision vars that has been replaced by individual decision vars
        // Delete until parsing.
        assert category.containsKey(name);
        categoryentry c = category.get(name);
        if (c.prev != null) {
            c.prev.next = c.next;
        } else {
            category_first = c.next;
        }
        if (c.next != null) {
            c.next.prev = c.prev;
        } else {
            category_last = c.prev;
        }
        category.remove(name);
        assert domains.containsKey(name);

        deleted_matrices.put(name, domains.get(name));
        domains.remove(name);
    }

    // Level of propagation in Minion when using -reduce-domains?
    public String minionReduceDomainsLevel() {
        String st = "SACBounds";        // default

        int numbounds =0;
        categoryentry itr = category_first;
        while (itr != null) {
            // Not auxiliary
            if (itr.cat == ASTNode.Decision || itr.cat == ASTNode.Auxiliary) {
                ArrayList<Intpair> setintervals = domains.get(itr.name).getIntervalSet();
                if (setintervals.size() > 0) {
                    long rangesize = setintervals.get(setintervals.size() - 1).upper - setintervals.get(0).lower + 1L;
                    if (rangesize > CmdFlags.getBoundVarThreshold()) {
                        if (rangesize > CmdFlags.getBoundVarThreshold() * 5) {
                            // If domain is 'really big' reduce prop level.
                            st = "GAC";
                        } else if (rangesize > CmdFlags.getBoundVarThreshold()) {
                            numbounds++;
                        }
                    }
                }
            }
            itr = itr.next;
        }
        if (numbounds > 5) {
            // If there are 'many' large variables, reduce prop level.
            st = "GAC";
        }
        return st;
    }
    
    
    
    //////////////////////////////////////////////////////////////////////////// 
    // 
    // Output methods

    // Mangling and demangling for serialization.

    private void mangle_before_serialization() {
        category_list = new ArrayList<categoryentry>();

        categoryentry cur = category_first;
        while (cur != null) {
            category_list.add(cur);
            cur = cur.next;
        }

        // unlink the list.
        cur = category_first;
        while (cur != null) {
            cur.prev = null;
            cur = cur.next;
            if (cur != null) {
                cur.prev.next = null;
            }
        }
    }

    public void unmangle_after_serialization() {
        if (category_list.size() > 0) {
            category_first = category_list.get(0);
            category_last = category_list.get(category_list.size() - 1);
        } else {
            category_first = null; category_last = null;
        }

        for (int i =0; i < category_list.size(); i++) {
            if (i > 0) {
                category_list.get(i).prev = category_list.get(i - 1);
            } else {
                category_list.get(i).prev = null;
            }

            if (i < category_list.size() - 1) {
                category_list.get(i).next = category_list.get(i + 1);
            } else {
                category_list.get(i).next = null;
            }
        }
        category_list = null;
    }
    
    protected void serialize() {
        mangle_before_serialization();
        try {
            FileOutputStream sts = new FileOutputStream(CmdFlags.auxfile);
            ObjectOutputStream out = new ObjectOutputStream(sts);
            out.writeObject(this);
            out.close();
            sts.close();
        } catch (Exception e) {
            CmdFlags.println(Thread.currentThread().getStackTrace());
            for (StackTraceElement t : e.getStackTrace()) {
                System.out.println(t);
            }
            CmdFlags.println("WARNING: Failed to serialise: " + e);
        }
        unmangle_after_serialization();
    }
    
    public void toMinion(BufferedWriter b) throws IOException {
        assert m.global_symbols == this;
        
        if(CmdFlags.getSaveSymbols()) {
            // Serialise the symbol table only if we are not running the back-end solver.
            serialize();
        }
        
        categoryentry itr = category_first;
        while (itr != null) {
            // Not auxiliary
            if (itr.cat == ASTNode.Decision) {
                output_variable(b, itr.name, (Domain) domains.get(itr.name));
            }
            itr = itr.next;
        }
        
        // Now do auxiliaries
        itr = category_first;
        while (itr != null) {
            if (itr.cat == ASTNode.Auxiliary) {
                output_variable(b, itr.name, (Domain) domains.get(itr.name));
            }
            itr = itr.next;
        }
    }

    public void printPrintStmt(BufferedWriter b) throws IOException {
        b.append("PRINT[");
        String sep = "";
        categoryentry itr = category_first;
        while (itr != null) {
            String name = itr.name;
            
            if (itr.cat == ASTNode.Decision) {                // Not auxiliary
                b.append(sep);
                if (getDomain(name) instanceof SimpleDomain) {
                    b.append("[");
                    b.append(name);
                    b.append("]");
                } else {
                    b.append(name);
                }
                sep = ",";
            }
            itr = itr.next;
        }
        // Objective -- last.
        if(m.objective!=null) {
            b.append("[");
            b.append(m.objective.getChild(0).toString());
            b.append("]");
        }
        
        b.append("]\n");
    }

    public void printAllVariables(Writer b, int cat) throws IOException {
        String sep = "";
        categoryentry itr = category_first;
        while (itr != null) {
            String name = itr.name;            // (String) d.getKey();

            if (itr.cat == cat) {
                b.append(sep);
                b.append(name);
                sep = ",";
            }
            itr = itr.next;
        }

    }
    
    //  Only prints one of a boolean/integer pair.
    public boolean printAllVariablesFlatzinc(StringBuilder b, int cat) {
        String sep = "";
        categoryentry itr = category_first;
        boolean hasVariables=false;
        while (itr != null) {
            String name = itr.name;
            
            if (itr.cat == cat) {
                b.append(sep);
                ASTNode dom=getDomain(name);
                if (dom.isBooleanSet() || (dom.isIntegerSet() && dom.getBounds().equals(new Intpair(0,1)))) {
                    if (boolvar_int.containsKey(name)) {
                        b.append(name + "_INTEGER");
                    } else if (boolvar_bool.containsKey(name)) {
                        b.append(name + "_BOOL");
                    } else {
                        assert false : "Something strange has happened: var with name " + name + " is apparently not used anywhere.";
                    }
                } else {
                    b.append(name);
                }
                hasVariables=true;
                sep = ",";
            }
            itr = itr.next;
        }
        return hasVariables;
    }
    
    public boolean printAllVariablesFlatzincExcept(StringBuilder b, int cat, String except) {
        String sep = "";
        categoryentry itr = category_first;
        boolean hasVariables=false;
        while (itr != null) {
            String name = itr.name;
            
            if (itr.cat == cat && ! name.equals(except)) {
                b.append(sep);
                ASTNode dom=getDomain(name);
                if (dom.isBooleanSet() || (dom.isIntegerSet() && dom.getBounds().equals(new Intpair(0,1)))) {
                    if (boolvar_int.containsKey(name)) {
                        b.append(name + "_INTEGER");
                    } else if (boolvar_bool.containsKey(name)) {
                        b.append(name + "_BOOL");
                    } else {
                        assert false : "Something strange has happened: var with name " + name + " is apparently not used anywhere.";
                    }
                } else {
                    b.append(name);
                }
                hasVariables=true;
                sep = ",";
            }
            itr = itr.next;
        }
        return hasVariables;
    }
    
    // Output variable declarations.
    private void output_variable(BufferedWriter b, String name, Domain dom) throws IOException {
        String ct = represents_ct.get(name);
        if (ct == null) {
            ct = "";
        }
        if (dom.isBooleanSet() && dom.containsValue(0) && dom.containsValue(1)) {
            b.append("BOOL " + name + " #" + ct + "\n");
        } else if (dom instanceof SimpleDomain) {
            ArrayList<Intpair> setintervals = dom.getIntervalSet();
            if (setintervals.size() > 0) {
                long rangesize = setintervals.get(setintervals.size() - 1).upper - setintervals.get(0).lower + 1L;

                if (CmdFlags.getUseBoundVars() && rangesize > CmdFlags.getBoundVarThreshold()) {
                    b.append("BOUND " + name + " #" + ct + "\n");
                } else {
                    b.append("DISCRETE " + name + " #" + ct + "\n");
                }

                b.append("{" + setintervals.get(0).lower + ".." + setintervals.get(setintervals.size() - 1).upper + "}\n");
                if (setintervals.size() > 1) {                    // It's not a complete range; need to knock out some vals.
                    b.append("**CONSTRAINTS**\n");
                    b.append("w-inintervalset(" + name + ", [");
                    for (int i =0; i < setintervals.size(); i++) {
                        b.append(String.valueOf(setintervals.get(i).lower));
                        b.append(",");
                        b.append(String.valueOf(setintervals.get(i).upper));
                        if (i < setintervals.size() - 1) {
                            b.append(",");
                        }
                    }
                    b.append("])\n");
                    b.append("**VARIABLES**\n");
                }
            } else {
                // Empty domain
                b.append("DISCRETE " + name + " #" + ct + "\n");
                b.append("{0..0}  #  This is an empty domain. Faking that by using 0..0 and the false() constraint below.\n");
                b.append("**CONSTRAINTS**\n");
                b.append("false()\n");
                b.append("**VARIABLES**\n");
            }
        } else {
            assert false;
        }

    }

    //////////////////////////////////////////////////////////////////////////// 
    // 
    // Dominion output

    public void toDominion(StringBuilder b) {
        TransformSimplify ts = new TransformSimplify();
        categoryentry itr = category_first;
        while (itr != null) {
            String name = itr.name;
            Domain dom = (Domain) getDomain(name);

            if (itr.cat == ASTNode.Parameter) {
                b.append("given " + name);
                if (dom instanceof MatrixDomain) {
                    MatrixDomain md = (MatrixDomain) dom;
                    b.append("[");
                    for (int i =3; i < md.numChildren(); i++) {
                        assert md.getChild(i).getBoundsAST().e1.equals(NumberConstant.make(0));
                        ASTNode upperbound = BinOp.makeBinOp("+", md.getChild(i).getBoundsAST().e2, NumberConstant.make(1));
                        upperbound = ts.transform(upperbound);
                        upperbound.toDominionParam(b);
                        if (i < md.numChildren() - 1) {
                            b.append(",");
                        }
                    }
                    b.append("]");
                    dom = (Domain) md.getChild(0);
                }
                b.append(": int {");
                dom.toDominionParam(b);
                b.append("}\n");
            } else if (itr.cat == ASTNode.Decision || itr.cat == ASTNode.Auxiliary) {
                output_variable_dominion(b, name, dom);
            } else if (itr.cat == ASTNode.ConstantMatrix) {
                m.cmstore.toDominion(b, itr.name);
            } else {
                CmdFlags.warning("Found entry in symbol table that cannot be output to Dominion: " + name);
            }
            
            itr = itr.next;
        }
    }

    // Output variable declarations, including matrices with conditions.
    // Switched this method over to toDominionParam.
    private void output_variable_dominion(StringBuilder b, String name, Domain dom) {
        String ct = represents_ct.get(name);
        if (ct == null) {
            ct = "";
        }
        if (dom.isBooleanSet()) {
            b.append("find " + name + " : bool $" + ct + "\n");
        } else if (dom instanceof SimpleDomain) {
            b.append("find " + name + " : int {");
            dom.toDominionParam(b);

            b.append("} $" + ct + "\n");
        } else if (dom instanceof MatrixDomain) {
            // Dim statement
            b.append("dim " + name + "[");
            ArrayList<ASTNode> doms = dom.getChildren();
            ASTNode basedom = doms.get(0);

            ArrayList<ASTNode> indices = new ArrayList<ASTNode>(doms.subList(3, doms.size()));
            ArrayList<ASTNode> dim_id = dom.getChild(1).getChildren();            // get contents of IdList
            ArrayList<ASTNode> conditions = new ArrayList<ASTNode>();
            if (dom.getChild(2) instanceof And) {
                conditions.addAll(dom.getChild(2).getChildren());
            } else if (!dom.getChild(2).equals(new BooleanConstant(true))) {
                conditions.add(dom.getChild(2));
            }

            assert indices.size() == dim_id.size() || dim_id.size() == 0;

            // List of dimension sizes
            for (int i =0; i < indices.size(); i++) {
                assert indices.get(i).getBoundsAST().e1.equals(NumberConstant.make(0));
                ASTNode upperbound = BinOp.makeBinOp("+", indices.get(i).getBoundsAST().e2, NumberConstant.make(1));
                TransformSimplify ts = new TransformSimplify();
                upperbound = ts.transform(upperbound);
                upperbound.toDominionParam(b);
                if (i < indices.size() - 1) {
                    b.append(",");
                }
            }
            b.append("] : int\n");

            if (dim_id.size() == 0) {
                // find statement for whole matrix.
                b.append("find " + name + "[");
                for (int i =0; i < indices.size(); i++) {
                    b.append("..");
                    if (i < indices.size() - 1) {
                        b.append(",");
                    }
                }
                b.append("] : int {");

                basedom.toDominionParam(b);
                b.append("}\n");

            } else {
                // Find comprehension.
                b.append("[ find " + name + "[");

                for (int i =0; i < dim_id.size(); i++) {
                    dim_id.get(i).toDominionParam(b);
                    if (i < dim_id.size() - 1) {
                        b.append(",");
                    }
                }

                b.append("]: int {");
                basedom.toDominionParam(b);
                b.append("} | ");

                // Now print the domains of each dim_id
                for (int i =0; i < dim_id.size(); i++) {
                    dim_id.get(i).toDominionParam(b);
                    b.append(" in {");
                    indices.get(i).toDominionParam(b);
                    b.append("}");
                    if (i < dim_id.size() - 1) {
                        b.append(", ");
                    }
                }

                // Now the conditions.
                if (conditions.size() > 0) {
                    b.append(", ");
                }
                for (int i =0; i < conditions.size(); i++) {
                    conditions.get(i).toDominionParam(b);
                    if (i < conditions.size() - 1) {
                        b.append(", ");
                    }
                }

                b.append("]\n");
            }
            if (! ct.equals("")) {
                b.append("$ representing constraint: " + ct + "\n");
            }
        } else {
            assert false;
        }

    }

    //////////////////////////////////////////////////////////////////////////// 
    // 
    // Flatzinc output
    
    // Methods for marking BooleanDomain variables as bool or int or both.
    
    public void markAsBoolFlatzinc(String name) {
        boolvar_bool.put(name, true);
    }

    public void markAsIntFlatzinc(String name) {
        boolvar_int.put(name, true);
    }

    public void toFlatzinc(BufferedWriter b) throws IOException {
        StringBuilder constraints = new StringBuilder();
        categoryentry itr = category_first;
        while (itr != null) {
            String name = itr.name;
            Domain dom = (Domain) getDomain(name);

            // Not auxiliary
            if (itr.cat == ASTNode.Decision) {
                output_variable_flatzinc(b, name, dom, constraints);
            }
            itr = itr.next;
        }

        // Now do auxiliaries
        itr = category_first;
        while (itr != null) {
            String name = itr.name;
            Domain dom = (Domain) getDomain(name);

            // Not auxiliary
            if (itr.cat == ASTNode.Auxiliary) {
                output_variable_flatzinc(b, name, dom, constraints);
            }
            itr = itr.next;
        }
        
        // Now dump the new constraints into b.
        b.append(constraints);

        // bool2int constraints
        itr = category_first;
        while (itr != null) {
            String name = itr.name;
            Domain dom = (Domain) getDomain(name);

            if((itr.cat == ASTNode.Decision || itr.cat == ASTNode.Auxiliary) && (dom.isBooleanSet() || (dom.isIntegerSet() && dom.getBounds().equals(new Intpair(0,1)))) 
                && boolvar_bool.containsKey(name) && boolvar_int.containsKey(name)) {
                b.append("constraint bool2int(" + name + "_BOOL," + name + "_INTEGER);\n");
            }
            itr = itr.next;
        }
    }
    
    // Output variable declarations.
    private void output_variable_flatzinc(BufferedWriter b, String name, Domain dom, StringBuilder c) throws IOException {
        // b is for variables, c is for constraints.
        String ct = represents_ct.get(name);
        if (ct == null) {
            ct = "";
        }
        if (dom.isBooleanSet() || (dom.isIntegerSet() && dom.getBounds().equals(new Intpair(0,1)))) {
            if (boolvar_bool.containsKey(name)) {
                b.append("var bool: " + name + "_BOOL");
                // i.e. not auxiliary and not also present as an int.
                if (category.get(name).cat == ASTNode.Decision && !boolvar_int.containsKey(name)) {
                    b.append("::output_var");
                }
                b.append("; %" + ct + "\n");
            }
            if (boolvar_int.containsKey(name)) {
                b.append("var {0,1}: " + name + "_INTEGER ");
                // i.e. not auxiliary
                if (category.get(name).cat == ASTNode.Decision) {
                    b.append("::output_var");
                }
                b.append("; %" + ct + "\n");
            }
        } else if (dom instanceof SimpleDomain) {
            ArrayList<Intpair> set = dom.getIntervalSet();
            if(set.size()==0) {
                b.append("var 0..0 : " + name);
                if (category.get(name).cat == ASTNode.Decision) {
                    b.append("::output_var");
                }
                b.append("; % Empty domain simulated with 0..0 and bool_eq(true,false). " + ct + "\n");
                c.append("constraint bool_eq(true,false);\n");  // Empty domain. 
            }
            else {
                b.append("var " + set.get(0).lower + ".." + set.get(set.size()-1).upper + ": " + name);
                // i.e. not auxiliary
                if (category.get(name).cat == ASTNode.Decision) {
                    b.append("::output_var");
                }
                b.append("; %" + ct + "\n");
    
                if (set.size() > 1) {                // It's not a complete range
                    c.append("constraint set_in(" + name + ",{");
                    for (int i =0; i < set.size(); i++) {
                        for (long j = set.get(i).lower; j <= set.get(i).upper; j++) {
                            c.append(j);
                            if (i < set.size() - 1 || j < set.get(i).upper) {
                                c.append(",");
                            }
                        }
                    }

                    c.append("});\n");
                }
            }
        } else {
            assert false;
        }

    }
    
    //////////////////////////////////////////////////////////////////////////// 
    // Minizinc
    
    public void toMinizinc(StringBuilder b) {
        if(CmdFlags.getSaveSymbols()) {
            // Serialise the symbol table only if given the save symbols flag.
            serialize();
        }
        
        categoryentry itr = category_first;
        while (itr != null) {
            String name = itr.name;
            Domain dom = (Domain) getDomain(name);

            // Not auxiliary
            if (itr.cat == ASTNode.Decision) {
                output_variable_minizinc(b, name, dom, false);
            }
            itr = itr.next;
        }

        // Now do auxiliaries
        itr = category_first;
        while (itr != null) {
            String name = itr.name;
            Domain dom = (Domain) getDomain(name);

            // Not auxiliary
            if (itr.cat == ASTNode.Auxiliary) {
                output_variable_minizinc(b, name, dom, true);
            }
            itr = itr.next;
        }
        
        // Link boolean and integer variables.
        itr = category_first;
        while (itr != null) {
            String name = itr.name;
            Domain dom = (Domain) getDomain(name);

            if ((itr.cat == ASTNode.Decision || itr.cat == ASTNode.Auxiliary) && (dom.isBooleanSet() || (dom.isIntegerSet() && dom.getBounds().equals(new Intpair(0,1)))) 
                && boolvar_bool.containsKey(name) && boolvar_int.containsKey(name)) {
                b.append("constraint bool2int(" + name + "_BOOL) = " + name + "_INTEGER;\n");
            }
            itr = itr.next;
        }
    }
    
    // Output variable declarations -- minizinc
    private void output_variable_minizinc(StringBuilder b, String name, Domain dom, boolean isAux) {
        String ct = represents_ct.get(name);
        if (ct == null) {
            ct = "";
        }
        String annot=isAux?" :: var_is_introduced :: is_defined_var ":"";
        
        if(dom.isBooleanSet() || (dom.isIntegerSet() && dom.getBounds().equals(new Intpair(0,1)))) {
            if (boolvar_bool.containsKey(name)) {
                b.append("var bool: " + name + "_BOOL"+annot+"; %" + ct + "\n");
            }
            if (boolvar_int.containsKey(name)) {
                b.append("var {0,1}: " + name + "_INTEGER"+annot+"; %" + ct + "\n");
            }
        }
        else if(dom instanceof SimpleDomain) {
            ArrayList<Intpair> set = dom.getIntervalSet();
            if (set.size() > 1) {                // It's not a complete range:
                // Output something like this:
                // set of int: aux1765 = 2..5 union 10..20;
                // var aux1765 : x;
                String setname = newAuxId();
                b.append("set of int : " + setname + " = ");
                for (int i =0; i < set.size(); i++) {
                    b.append(set.get(i).lower + ".." + set.get(i).upper);
                    if (i < set.size() - 1) {
                        b.append(" union ");
                    }
                }
                b.append(";\n");
                b.append("var " + setname + " : " + name);

            } else {
                b.append("var " + set.get(0).lower + ".." + set.get(0).upper + ": " + name);
            }
            b.append(annot);
            b.append("; %" + ct + "\n");
        }
        else {
            assert false;
        }
    }
    
    public void showVariablesMinizinc(StringBuilder b) {
        categoryentry itr = category_first;
        boolean trailingcomma = false;
        while (itr != null) {
            String name = itr.name;
            Domain dom = (Domain) getDomain(name);

            // Not auxiliary
            if (itr.cat == ASTNode.Decision) {
                b.append("show(");

                if (dom.isBooleanSet() || (dom.isIntegerSet() && dom.getBounds().equals(new Intpair(0,1)))) {
                    if (boolvar_bool.containsKey(name)) {
                        b.append(name + "_BOOL");
                    } else if (boolvar_int.containsKey(name)) {
                        b.append(name + "_INTEGER");
                    }
                } else {
                    b.append(name);
                }

                b.append("),\" \",");
                trailingcomma = true;
            }
            itr = itr.next;
        }

        // take off trailing comma.
        if (trailingcomma) {
            b.deleteCharAt(b.length() - 1);
        }
    }
    
    ////////////////////////////////////////////////////////////////////////////
    // Data and functions for SAT output.
    
    public void markAsDirectSAT(String name) {
        if(directvar_sat==null) directvar_sat=new HashSet<String>();
        directvar_sat.add(name);
    }
    
    public boolean isDirectSAT(String name) {
        if(directvar_sat==null) {
            return false;
        }
        else {
            return directvar_sat.contains(name);
        }
    }
    
    //////////////////////////////////////////////////////////////////////////// 
    // JSON output of model

    public void writeVarDomainsAsJSON(StringBuilder bf) {
        bf.append("[");
        categoryentry c = category_first;
        boolean decisionFound = false;
        while (c != null) {
            if (c.cat == ASTNode.Decision) {
                if (decisionFound) {
                    bf.append(",");
                } else {
                    decisionFound = true;
                }
                bf.append("\n");
                ASTNode domain = getDomain(c.name);
                bf.append("{\n\"name\": \"" + escapeVar(c.name) + "\",\n");
                bf.append("\"domain\": [");
                ArrayList<Intpair> domPairs = domain.getIntervalSet();
                for (int i = 0; i < domPairs.size(); i++) {
                    bf.append("[" + domPairs.get(i).lower + ", " + domPairs.get(i).upper + "]");
                    if (i < domPairs.size() - 1) {
                        bf.append(",");
                    }
                }
                bf.append("]\n}");
            }

            c = c.next;
        }
        bf.append("]");
    }

    public void writeVarListAsJSON(StringBuilder bf) {
        bf.append("[");
        categoryentry c = category_first;
        boolean decisionFound = false;
        while (c != null) {
            if (c.cat == ASTNode.Decision) {
                if (decisionFound) {
                    bf.append(",");
                } else {
                    decisionFound = true;
                }
                bf.append("\"" + escapeVar(c.name) + "\"");
            }
            c = c.next;
        }
        bf.append("]");
    }

    String escapeVar(String s) {
        return "$" + s;
    }

    
    public static String unescapeVar(String s) {
        return s.replaceAll("^\\$(.*)$", "$1");
    }
    
    public ArrayList<String>  getVarNamesList() {
        ArrayList<String> vars = new ArrayList<String>();
        categoryentry c = category_first;
        boolean decisionFound = false;
        while (c != null) {
            if (c.cat == ASTNode.Decision) {
                vars.add(c.name);
            }
            c = c.next;
        }
        return vars;
    }
}
