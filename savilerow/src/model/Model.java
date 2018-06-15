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
import java.util.*;
import java.io.*;

// Contains a CSP.

public class Model
{
    public ASTNode constraints;
    
    public SymbolTable global_symbols;
    
    public FilteredDomainStore filt;
    
    public ConstantMatrixStore cmstore;
    
    public ASTNode objective;
    
    public ASTNode branchingon;   // should be a 1-d matrix (or concatenate, or flatten..)
    
    public String heuristic;
    
    public ASTNode sns;   // Container for SNS related things
    
    public Sat satModel;
    
    public ASTNode incumbentSolution;    // For optimisation using multiple solvers, intermediate solutions stored here. 
    
    //  Make an empty model to be populated using one of the setup methods.
    public Model() {
    }
    
    //  This one for construction in the parser.
    public void setup(ASTNode c, SymbolTable st, ASTNode ob, ASTNode branch, String h, ASTNode _sns)
    {
        assert c!=null;
        assert st!=null;
        
        constraints=c;
        global_symbols=st;
        st.m=this;
        objective=ob;
        branchingon=branch;
        heuristic=h;
        
        setDefaultBranchingOn();
        
        // Make a filt.
        filt=new FilteredDomainStore(global_symbols);
        cmstore=new ConstantMatrixStore(this);
        
        sns=_sns;
    }
    
    public void setup(ASTNode c, SymbolTable st, FilteredDomainStore f, ConstantMatrixStore cm, ASTNode ob, ASTNode branch, String h, ASTNode _sns)
    {
        assert c!=null;
        assert st!=null;
        
        constraints=c;
        global_symbols=st;
        st.m=this;
        objective=ob;
        branchingon=branch;
        heuristic=h;
        
        setDefaultBranchingOn();
        
        filt=f;
        cmstore=cm;
        cm.m=this;
        
        sns=_sns;
    }
    
    private void setDefaultBranchingOn() {
        // Make a default branching on list if there isn't one.
        if(branchingon==null) {
            ArrayList<ASTNode> letgivs=new ArrayList<ASTNode>(global_symbols.lettings_givens);
            ArrayList<ASTNode> bran=new ArrayList<ASTNode>();
            for(int i=0; i<letgivs.size(); i++) {
                if(letgivs.get(i) instanceof Find) {
                    if(letgivs.get(i).getChild(1) instanceof MatrixDomain) {
                        bran.add(new Flatten(letgivs.get(i).getChild(0)));
                    }
                    else {
                        ArrayList<ASTNode> tmp=new ArrayList<ASTNode>();
                        tmp.add(letgivs.get(i).getChild(0));
                        bran.add(new CompoundMatrix(tmp));
                    }
                }
            }
            
            branchingon=new Concatenate(bran);
        }
    }
    
    // Simplify the model in-place.
    public void simplify()
    {
        //AuditTreeLinks atl=new AuditTreeLinks();
        TransformSimplify ts=new TransformSimplify();
        
        //atl.transform(constraints);
        boolean sat=global_symbols.simplify();   // return value -- true means no empty domains. 
        
        //  Constraints must go before objective, branching on because constraints may
        //  generate variable assignments, unification.
        if(!sat) {
            constraints=new Top(new BooleanConstant(false));
        }
        else {
            if(CmdFlags.getUseDeleteVars()) {
                TransformSimplifyExtended tse=new TransformSimplifyExtended(this);
                constraints=tse.transform(constraints);  // Does the extended one only on the constraints.
            }
            else {
                constraints=ts.transform(constraints);   
            }
        }
        
        if(objective!=null) {
            objective=ts.transform(objective);
            if(objective.getChild(0).isConstant()) {
                CmdFlags.println("Dropping objective: "+objective);
                objective=null;  // Throw away the objective if the expression inside has become a constant. 
            }
        }
        if(branchingon!=null) {
            branchingon=ts.transform(branchingon);
        }
        
        // SNS related things
        if(sns!=null) {
            sns=ts.transform(sns);
        }
        
        
        
        filt.simplify();    //  Allows FilteredDomainStore to get rid of any assigned vars in its stored expressions.
    }
    
    // Substitute an expression throughout.
    // This is used to implement letting. 
    public void substitute(ASTNode toreplace, ASTNode replacement)
    {
        ReplaceASTNode t=new ReplaceASTNode(toreplace, replacement);
        constraints=t.transform(constraints);
        
        if(objective!=null)
            objective=t.transform(objective);
        
        if(branchingon!=null)
            branchingon=t.transform(branchingon);
        
        if(sns!=null) {
            sns=t.transform(sns);
        }
        
        global_symbols.substitute(toreplace, replacement);
    }
    
    public boolean typecheck() {
        
        // Branching on.
        if(branchingon!=null && branchingon.getDimension()!=1) {
            CmdFlags.println("ERROR: 'branching on' statement may only contain 1-dimensional matrices of decision variables.");
            return false;
        }
        
        //  Objective
        if(objective!=null) {
            if(!objective.typecheck(global_symbols)) return false;
            if(! (objective instanceof Maximising || objective instanceof Minimising) ) {
                CmdFlags.println("ERROR: Objective: "+objective);
                CmdFlags.println("ERROR: should be either minimising or maximising.");
                return false;
            }
            
            if( (!objective.getChild(0).isNumerical()) && (!objective.getChild(0).isRelation()) ) {
                CmdFlags.println("ERROR: Objective must be numerical or relational.");
                return false;
            }
        }
        
        if(sns!=null && !sns.typecheck(global_symbols)) return false;
        
        if(!constraints.typecheck(global_symbols)) return false;
        if(!global_symbols.typecheck()) return false;
        if(!cmstore.typecheck()) return false;
        return true;
    }
    
    // Given a tree transformer, apply it to this model. 
    public boolean transform(TreeTransformer t) {
        if(CmdFlags.getVerbose()) {
            System.out.println("Rule:"+t.getClass().getName());
        }
        boolean changedModel=false;
        
        assert constraints instanceof Top;
        
        constraints=t.transform(constraints);
        changedModel=changedModel || t.changedTree;
        
        if(objective!=null) {
            objective=t.transform(objective);
            changedModel=changedModel || t.changedTree;
        }
        
        if(t.getContextCts()!=null) {
            // Extra constraints from the objective. 
            ASTNode bob=t.getContextCts();
            constraints.getChild(0).setParent(null); /// Do not copy all the constraints
            constraints=new Top(new And(constraints.getChild(0), bob));
            changedModel=true;
            
            // Replace objective with 0 when generated constraint is false.
            
            ASTNode newObj=new MatrixDeref(
                new CompoundMatrix(new IntegerDomain(new Range(NumberConstant.make(0), NumberConstant.make(1))), ASTNode.list(NumberConstant.make(0), objective.getChild(0))),  //  Indexed by 0..1
                ASTNode.list(bob));   // Indexed by the new constraint, so the objective function becomes 0 when the constraint is false.  
            
            objective.setChild(0, newObj);
        }
        
        // WHY not domains??
        
        //  Branching on
        assert branchingon!=null;
        branchingon=t.transform(branchingon);
        changedModel=changedModel || t.changedTree;
        
        if(t.getContextCts()!=null) {
            // Extra constraints from branchingOn
            constraints.getChild(0).setParent(null); /// Do not copy all the constraints
            constraints=new Top(new And(constraints.getChild(0), t.getContextCts()));
            changedModel=true;
        }
        
        if(sns!=null) {
            sns=t.transform(sns);
            changedModel=changedModel || t.changedTree;
            if(t.getContextCts()!=null) {
                // Extra constraints from sns
                constraints.getChild(0).setParent(null); /// Do not copy all the constraints
                constraints=new Top(new And(constraints.getChild(0), t.getContextCts()));
                changedModel=true;
            }
        }
        
        if(CmdFlags.getVerbose() && changedModel) {
            System.out.println("Model has changed. Model after rule application:\n"+this.toString());
        }
        
        if(changedModel) {
            simplify();
            
            if(CmdFlags.getVerbose()) {
                System.out.println("Model after rule application and simplify:\n"+this.toString());
            }
        }
        
        assert constraints instanceof Top;
        return changedModel;
    }
    
    @Override
    public int hashCode() {
        return constraints.hashCode() 
        ^ global_symbols.hashCode() 
        ^ filt.hashCode() 
        ^ cmstore.hashCode() 
        ^ (objective==null?0:objective.hashCode()) 
        ^ branchingon.hashCode() 
        ^ (heuristic==null?0:heuristic.hashCode()) 
        ^ (incumbentSolution==null?0:incumbentSolution.hashCode())
        ^ (sns==null?0:sns.hashCode());
    }
    
    @Override
    public boolean equals(Object b)
    {
        if(this.getClass() != b.getClass())
            return false;
        Model c=(Model)b;
        
        if(! c.constraints.equals(constraints))
            return false;
        if(! c.global_symbols.equals(global_symbols))
            return false;
        if(! c.filt.equals(filt))
            return false;
        if(! c.cmstore.equals(cmstore))
            return false;
        
        if( !(  objective==null ? c.objective==null : objective.equals(c.objective)))
            return false;
        if(! branchingon.equals(c.branchingon))
            return false;
        if( !( heuristic==null ? c.heuristic==null : heuristic.equals(c.heuristic)))
            return false;
        if( !( incumbentSolution==null ? c.incumbentSolution==null : incumbentSolution.equals(c.incumbentSolution)))
            return false;
        if( !( sns==null ? c.sns==null : sns.equals(c.sns)))
            return false;
        
        return true;
    }
    
    public Model copy() {
        // Make an empty model to populate.
        Model newmodel=new Model();
        
        // Copy symbol table first.
        SymbolTable newst=global_symbols.copy(newmodel);
        FilteredDomainStore f=filt.copy(newst);
        //  Identifiers have a reference to the original symbol table. Fix it to point to the copy.
        TransformFixSTRef tf=new TransformFixSTRef(newmodel);
        
        ASTNode newct=tf.transform(constraints.copy());
        
        ASTNode ob=null;
        if(objective!=null) ob=tf.transform(objective.copy());
        
        ASTNode bran=tf.transform(branchingon.copy());
        
        ConstantMatrixStore cmst=cmstore.copy(newmodel);
        
        ASTNode snscopy=null;
        if(sns!=null) snscopy=tf.transform(sns.copy());
        
        newmodel.setup(newct, newst, f, cmst, ob, bran, heuristic, snscopy);
        
        if(incumbentSolution!=null) {
            newmodel.incumbentSolution=tf.transform(incumbentSolution.copy());
        }
        
        return newmodel;
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //   Output methods. 
    
    public void toMinion(BufferedWriter b) throws IOException {
        toMinion(b, null);
    }
    
    // Output to minion
    public void toMinion(BufferedWriter b, ArrayList<ASTNode> scope) throws IOException {
        b.append("MINION 3\n");
        
        for (String key : CmdFlags.stats.keySet()) {
            b.append("# "+key+" = "+CmdFlags.stats.get(key)+"\n");
        }
        
        b.append("**VARIABLES**\n");    
        global_symbols.toMinion(b);
        cmstore.toMinion(b);
        
        b.append("**SEARCH**\n");
        if(scope==null) {
            global_symbols.printPrintStmt(b);
        }
        else {
            b.append("PRINT [");
            for(int i=0; i<scope.size(); i++) {
                b.append("[");
                scope.get(i).toMinion(b, false);
                b.append("]");
                if(i<scope.size()-1) b.append(",");
            }
            b.append("]\n");
        }
        
        if(objective!=null)
            objective.toMinion(b, false);
        
        if(scope!=null) {
            b.append("VARORDER [");
            for(int i=0; i<scope.size(); i++) {
                scope.get(i).toMinion(b, false);
                //b.append(scope.get(i));
                if(i<scope.size()-1) b.append(",");
            }
            b.append("]\n");
        }
        else if(branchingon!=null) {
            b.append("VARORDER ");
            if(heuristic!=null) {
                b.append(heuristic);
            }
            else {
                // default var ordering
                b.append("STATIC");
            }
            b.append(" ");
            
            branchingon.toMinion(b, false);
            b.append("\n");
            
            // put ALL variables into a varorder aux, this ensures they'll all 
            // be assigned in any solution produced by minion.
            b.append("VARORDER AUX [");
            StringWriter decVarsBuffer = new StringWriter();
            global_symbols.printAllVariables(decVarsBuffer, ASTNode.Decision);
            
            StringWriter auxVarsBuffer = new StringWriter();
            global_symbols.printAllVariables(auxVarsBuffer, ASTNode.Auxiliary);
            if(decVarsBuffer.getBuffer().length()>0) {
                b.append(decVarsBuffer.getBuffer());
                if(auxVarsBuffer.getBuffer().length()>0) {
                    b.append(",");
                    b.append(auxVarsBuffer.getBuffer());
                }
            }
            else {
                if(auxVarsBuffer.getBuffer().length()>0) {
                    b.append(auxVarsBuffer.getBuffer());
                }
            }
            b.append("]\n");
        }
        else {
            // Only have heuristic and not branching on.
            if(heuristic!=null) {
                b.append("VARORDER "+heuristic+" ["); 
            }
            else{
                b.append("VARORDER STATIC [");
            }
            
            global_symbols.printAllVariables(b, ASTNode.Decision);
            b.append("]\n");
            
            b.append("VARORDER AUX [");
            global_symbols.printAllVariables(b, ASTNode.Auxiliary);
            b.append("]\n");
        }
        
        b.append("**CONSTRAINTS**\n");
        constraints.toMinion(b, true);
        
        // SNS
        if(sns!=null) {
            sns.toMinion(b, false);
        }
        
        b.append("**EOF**\n");
    }
    
    public void toDominion(StringBuilder b) {
        b.append("language Dominion 0.0\n");
        
        // Variables, parameters etc
        global_symbols.toDominion(b);
        
        // Optimisation 
        if(objective!=null)
            objective.toDominion(b, false);
        
        b.append("such that\n");
        constraints.toDominion(b, true);
        b.append("\n");
    }
    
    // Output the model in Essence' eventually
    public String toString() {
        StringBuilder s=new StringBuilder();
        s.append("language ESSENCE' 1.0\n");
        s.append(global_symbols.toString());
        if(objective!=null) s.append(objective.toString());
        if(sns!=null) {
            s.append(sns.toString());
        }
        s.append("such that\n");
        s.append(constraints.toString());
        //s.append(filt.toString());
        return s.toString();
    }
    
    public void toFlatzinc(BufferedWriter b) throws IOException {
        //StringBuilder b=new StringBuilder();
        // get access to some predicates in gecode.
        b.append("predicate all_different_int(array [int] of var int: xs);\n");
        if(CmdFlags.getGecodetrans()) {
            b.append("predicate gecode_global_cardinality(array[int] of var int: x, array[int] of int: cover, array[int] of var int: counts);");
        }
        
        cmstore.toFlatzinc(b);
        global_symbols.toFlatzinc(b);
        
        constraints.toFlatzinc(b, true);
        
        b.append("solve :: int_search(");
        
        if(branchingon instanceof EmptyMatrix) {
            b.append("[1]");  // Gecode needs something in the list. 
        }
        else {
            branchingon.toFlatzinc(b, false);
        }
        
        b.append(", input_order, indomain_min, complete)\n");
        
        if(objective!=null)
            objective.toFlatzinc(b, false);
        else
            b.append(" satisfy;\n");
        
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //  Minizinc output
    
    public void toMinizinc(StringBuilder b) {
        b.append("% Minizinc model produced by Savile Row from Essence Prime file "+CmdFlags.eprimefile);
        if(CmdFlags.paramfile!=null) b.append(" and parameter file "+CmdFlags.paramfile);
        b.append("\n");
        
        b.append("include \"globals.mzn\";\n");
        
        if(CmdFlags.getMznLNS()) {
            b.append("include \"minisearch.mzn\";\n");
        }
        
        global_symbols.toMinizinc(b);
        cmstore.toMinizinc(b);
        constraints.toMinizinc(b, true);
        
        if(CmdFlags.getMznLNS()) {
            // Generate Minisearch auto LNS annotation.
            assert objective!=null;
            /*
            int: iterations = 100;
            int: initRate = 20; % start with destroying 20%
            int: time_ms = 5*1000;
            solve search adaptive_lns_min(obj, x, iterations, initRate, time_ms);*/
            
            b.append("solve search adaptive_lns_");
            if(objective instanceof Minimising) {
                b.append("min(");
            }
            else {
                b.append("max(");
            }
            objective.getChild(0).toMinizinc(b, false);
            
            b.append(", [");
            //  Add all non-auxiliary variables
            global_symbols.printAllVariablesFlatzincExcept(b, ASTNode.Decision, objective.getChild(0).toString());
            b.append("], 1000000, 10, 5000);\n");
        }
        else {
            //  A search annotation with a static variable ordering. 
            b.append("solve :: int_search([");
            
            // Search order annotation. Should look at branchingon.
            global_symbols.printAllVariablesFlatzinc(b, ASTNode.Decision);
            
            b.append("], input_order, indomain_min, complete)\n");
            
            if(objective!=null)
                objective.toMinizinc(b, false);
            else
                b.append(" satisfy;\n");
        }
        
        b.append("output\n [");
        
        global_symbols.showVariablesMinizinc(b);
        
        if(objective!=null) b.append(",show("+objective.getChild(0).toString()+")");
        
        b.append("];\n");
    }
    
    public boolean setupSAT(HashSet<String> varsInConstraints) {
        try {
            satModel=new Sat(this.global_symbols);
            satModel.generateVariableEncoding(varsInConstraints);
            return true;
        }
        catch(IOException e) {
            // Tidy up. 
            File f = new File(CmdFlags.satfile);
            if (f.exists()) f.delete();
            return false;
        }
    }
    
    public boolean toSAT()
    {
        try {
            constraints.toSAT(satModel);
            
            if(CmdFlags.getMaxsattrans() && objective!=null) {
                //  Encode the optimisation variable with soft clauses.
                objective.toSAT(satModel);
            }
            
            satModel.finaliseOutput();
            return true;
        }
        catch(IOException e) {
            // Tidy up.
            File f = new File(CmdFlags.satfile);
            if (f.exists()) f.delete();
            return false;
        }
    }
}
