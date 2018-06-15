package savilerow.solver;
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
import savilerow.expression.*;
import savilerow.CmdFlags;
import savilerow.eprimeparser.EPrimeReader;
import savilerow.treetransformer.*;

public abstract class Solver
{
    long solutionCounter=0;
    int numdigits=6;
    
    // Each Solver class implements a findSolutions method. Takes the name of the binary, filename of the problem
    // instance and the model. 
    public abstract void findSolutions(String solvername, String filename, Model m) throws IOException,  InterruptedException;
    
    // Definitely should be in Solver. 
    public void parseSolutionMode() {
        // First try to recover the symbol table. 
        SymbolTable st;
        try {
            FileInputStream sts=new FileInputStream(CmdFlags.auxfile);
            ObjectInputStream in = new ObjectInputStream(sts);
            st=(SymbolTable)in.readObject();
            st.unmangle_after_serialization();
            in.close();
            sts.close();
        } catch (Exception e) {
            CmdFlags.println(""+e);
            st=null;
        }
        
        if(st==null) {
            CmdFlags.errorExit("Failed to read serialisation file "+CmdFlags.auxfile);
        }
        
        // Parse temporary solution file.
        if((!CmdFlags.getFindAllSolutions()) && CmdFlags.getFindNumSolutions()==-1) {
            // Find one solution only. Takes the last solution because for optimisation that will be the optimal one.
            try {
                BufferedReader minsolfile=new BufferedReader(new FileReader(CmdFlags.minionsolfile));
                Solution sol = parseLastSolverSolution(st, minsolfile);
                
                createSolutionFile(sol, false);
            }
            catch(IOException e) {
                System.out.println("Could not open or parse Minion solution file. "+e);
            }
        }
        else {
            // Multiple solutions. 
            try {
                BufferedReader minsolfile=new BufferedReader(new FileReader(CmdFlags.minionsolfile));
                parseAllSolverSolutions(st, minsolfile);
            }
            catch(FileNotFoundException e) {
                System.out.println("Could not open or parse Minion solution file. "+e);
            }
        }
    }
    
    
    // Repeatedly calls parseOneSolverSolution 
    void parseAllSolverSolutions(SymbolTable st, BufferedReader in) {
        while(true) {
            Solution sol=parseOneSolverSolution(st, in);
            if(sol==null) {
                break;
            }
            
            createSolutionFile(sol, true);
            
            if(solutionCounter==CmdFlags.getFindNumSolutions()) {
                break;
            }
        }
    }
    
    abstract Solution parseOneSolverSolution(SymbolTable st, BufferedReader in);
    
    abstract Solution parseLastSolverSolution(SymbolTable st, BufferedReader in);
    
    // Parse a 'solver solution' (i.e. one solution in the text format output by the solver)
    // into a hashmap. 
    abstract HashMap<String, Long> readAllAssignments(ArrayList<String> solversolution, SymbolTable st);
    
    // Using readAllAssignments, turn a solver solution into a Savile Row solution. 
    Solution solverSolToAST(ArrayList<String> solversol, SymbolTable st) {
        ArrayList<ASTNode> solution=new ArrayList<ASTNode>();
        HashMap<String, HashMap<ArrayList<Long>, ASTNode>> collect_matrices=new HashMap<String, HashMap<ArrayList<Long>, ASTNode>>();
        
        HashMap<String, Long> collect_all_values=readAllAssignments(solversol, st);   // Collect the value of every variable,
        
        Long optval=null;
        // Retrieve the optimisation value.
        if(st.m!=null && st.m.objective!=null) {
            optval=collect_all_values.get(st.m.objective.getChild(0).toString());
        }
        
        categoryentry curcat=st.getCategoryFirst();
        
        // Iterate through decision variables in symbol table. 
        while(curcat!=null) {
            String name=curcat.name;
            int category=curcat.cat;
            
            if(category==ASTNode.Decision) {
                ASTNode domain=st.getDomain(name);
                
                assert domain.isFiniteSet();
                
                long i;
                if(collect_all_values.containsKey(name)) {
                    i = collect_all_values.get(name);
                }
                else if(collect_all_values.containsKey(name+"_INTEGER")) {
                    i = collect_all_values.get(name+"_INTEGER");
                }
                else if(collect_all_values.containsKey(name+"_BOOL")) {
                    i = collect_all_values.get(name+"_BOOL");
                }
                else {
                    if(CmdFlags.getSattrans()) {
                        // Value not given in solution. Can happen, e.g. when a SAT solver removes unused variables.
                        i = domain.getBounds().lower;
                    }
                    else {
                        return null;  //  Fail to parse a solution.  
                    }
                }
                
                if(st.replaces_matrix.containsKey(name)) {
                    // This is an individual decision variable that replaces a matrix
                    // Need to build up a matrix.
                    
                    if(!collect_matrices.containsKey(st.replaces_matrix.get(name).name)) {
                        // put in the empty matrix
                        collect_matrices.put(st.replaces_matrix.get(name).name, new HashMap<ArrayList<Long>, ASTNode>());
                    }
                    
                    if(domain.isBooleanSet()) {
                        collect_matrices.get(st.replaces_matrix.get(name).name)
                            .put(st.replaces_matrix.get(name).idx, new BooleanConstant( i!=0 ));
                    }
                    else {
                        collect_matrices.get(st.replaces_matrix.get(name).name)
                            .put(st.replaces_matrix.get(name).idx, NumberConstant.make(i));
                    }
                }
                else {
                    // read a single value.
                    if(domain.isBooleanSet()) {
                        solution.add(new Letting(new Identifier(st.m, name), new BooleanConstant( i!=0 )));
                    } 
                    else {
                        solution.add(new Letting(new Identifier(st.m, name), NumberConstant.make(i)));
                    }
                }
                
            }
            
            curcat=curcat.next;
        }
        
        //  Now iterate through deleted variables in 'replacements'
        for(ASTNode delvar : st.replacements.keySet()) {
            // No matrices.
            String name=delvar.toString();
            
            if(st.replacements_category.get(delvar)==ASTNode.Decision) {
                ASTNode replace=st.replacements.get(delvar);
                ASTNode domain=st.replacements_domains.get(delvar);
                
                // get the value of delvar. 
                long i=readReplacementValue(replace, collect_all_values, st.replacements);
                
                collect_all_values.put(name, i);
                
                if(st.replaces_matrix.containsKey(name)) {
                    // This is an individual decision variable that replaces a matrix
                    
                    // Need to do something different -- build up a matrix.
                    
                    if(!collect_matrices.containsKey(st.replaces_matrix.get(name).name)) {
                        // put in the empty matrix
                        collect_matrices.put(st.replaces_matrix.get(name).name, new HashMap<ArrayList<Long>, ASTNode>());
                    }
                    
                    if(domain.isBooleanSet()) {
                        collect_matrices.get(st.replaces_matrix.get(name).name)
                            .put(st.replaces_matrix.get(name).idx, new BooleanConstant( i!=0 ));
                    }
                    else {
                        collect_matrices.get(st.replaces_matrix.get(name).name)
                            .put(st.replaces_matrix.get(name).idx, NumberConstant.make(i));
                    }
                }
                else {
                    // read a single value.
                    if(domain.isBooleanSet()) {
                        solution.add(new Letting(new Identifier(st.m, name), new BooleanConstant( i!=0 )));
                    } 
                    else {
                        solution.add(new Letting(new Identifier(st.m, name), NumberConstant.make(i)));
                    }
                }
            }
        }
        
        
        // Now turn collect_matrices into matrices.  
        for(String matname : collect_matrices.keySet()) {
            // get index domains
            ASTNode matrixdom=st.deleted_matrices.get(matname);
            
            ArrayList<ASTNode> indexdoms=matrixdom.getChildren(3);
            
            boolean isBool=matrixdom.getChild(0).isBooleanSet();
            
            solution.add(new Letting(new Identifier(st.m, matname), collectMatrix(indexdoms, matname, new ArrayList<Long>(), collect_matrices, isBool) ) );
        }
        
        // Finally there may be some empty matrices. 
        for(String matname : st.deleted_matrices.keySet()) {
            if( ! collect_matrices.keySet().contains(matname)) {
                ASTNode value = new EmptyMatrix(st.deleted_matrices.get(matname));
                //  Put into normal form
                ASTNode valueNormalised = (new TransformSimplify()).transform(value);
                solution.add(new Letting(new Identifier(st.m, matname), valueNormalised));
            }
        }
        
        // Sort the letting statements alphabetically
        class cmplettings implements Comparator<ASTNode> {
            public int compare(ASTNode x, ASTNode y) {
                return x.getChild(0).toString().compareTo(y.getChild(0).toString());
            }
        }
        cmplettings cl=new cmplettings();
        Collections.sort(solution, cl);
        
        if(optval==null) {
            return new Solution(solution, new ArrayList<String>());
        }
        else {
            return new Solution(solution, new ArrayList<String>(), optval);
        }
    }
    
    
    private long readReplacementValue(ASTNode replace, HashMap<String, Long> collect_all_values, HashMap<ASTNode, ASTNode> replacements) {
        
        // Follow any further replacement links to get the final variable/value/expression
        while(replacements.get(replace)!=null) {
            replace=replacements.get(replace);
        }
        
        if(replace.isConstant()) {
            return replace.getValue();
        }
        else if(replace instanceof Identifier) {
            if(collect_all_values.containsKey(replace.toString())) {
                return collect_all_values.get(replace.toString());
            }
            else if(collect_all_values.containsKey(replace.toString()+"_INTEGER")) {
                return collect_all_values.get(replace.toString()+"_INTEGER");
            }
            else {
                return collect_all_values.get(replace.toString()+"_BOOL");
            }
        }
        else {
            // Not a constant or a bare identifier. 
            assert replace instanceof Negate;
            
            return 1-readReplacementValue(replace.getChild(0), collect_all_values, replacements);
        }
    }
    
    //  create vars M_1_1 for M[1,1]
    private ASTNode collectMatrix(ArrayList<ASTNode> idxdoms, String matname, ArrayList<Long> indices, HashMap<String, HashMap<ArrayList<Long>, ASTNode>> collect_matrices, boolean isBool) {
        if(idxdoms.size()==0) {
            if(collect_matrices.get(matname).containsKey(indices)) {
                return collect_matrices.get(matname).get(indices);   // NumberConstant
            }
            else {
                return new NoValue();
            }
        }
        else {
            ArrayList<ASTNode> localindexdoms=new ArrayList<ASTNode>(idxdoms);
            ASTNode idx=localindexdoms.remove(0);
            
            ArrayList<Long> valset=idx.getValueSet();
            ArrayList<ASTNode> mat=new ArrayList<ASTNode>();
            for(int i=0; i<valset.size(); i++) {
                indices.add(valset.get(i));
                mat.add(collectMatrix(localindexdoms, matname, indices, collect_matrices, isBool));
                indices.remove(indices.size()-1);
            }
            if(mat.size()>0) {
                return new CompoundMatrix(idx, mat);
            }
            else {
                if(isBool) {
                    return new EmptyMatrix(new MatrixDomain(new BooleanDomainFull(), idxdoms));
                }
                else {
                    return new EmptyMatrix(new MatrixDomain(new IntegerDomain(new EmptyRange()), idxdoms));
                }
            }
        }
    }
    
    //  Must be in Solver. 
    void createSolutionFile(ASTNode sol, boolean multipleSols) {
        String filename;
        if(multipleSols) {
            String fmtint=String.format("%0"+numdigits+"d",solutionCounter+1);
            solutionCounter++;
            filename=CmdFlags.solutionfile+"."+fmtint;
        }
        else {
            filename=CmdFlags.solutionfile;
        }
        
        if(CmdFlags.mining) {
            //  Store solutions.
            if(MultiStageOnSolution.sollist==null) {
                MultiStageOnSolution.sollist=new ArrayList<ASTNode>();
            }
            MultiStageOnSolution.sollist.add(sol);
        }
        if(CmdFlags.getSolutionsToNull()) {
            // do nothing. 
        }
        else if(CmdFlags.getSolutionsToStdout()) {
            // Just dump it to stdout.
            System.out.println(sol.toString());
            System.out.println("----------");
        }
        else if(CmdFlags.getSolutionsToStdoutOneLine()) {
            // Dump it to stdout, one solution per line.
            System.out.println("Solution: " + ((Solution) sol).toStringOneLine().replaceAll("[\\t\\n\\r]", " "));
        }
        else {
            try {
                BufferedWriter out;
                out= new BufferedWriter(new FileWriter(filename));
                out.write(sol.toString());
                out.close();
                CmdFlags.println("Created solution file " + filename);
            }
            catch (IOException e) {
                CmdFlags.println("Could not open file for solution output.");
            }
        }
    }
    
    void checkSolution(HashMap<String, Long> solverSolution) {
        // Retrieve the model that was stored before encoding / solver-specific transformations. 
        
        Model m=CmdFlags.checkSolModel;
        
        // Check each constraint in turn. 
        
        ArrayList<ASTNode> cts;
        assert m.constraints instanceof Top;
        if(m.constraints.getChild(0) instanceof And) {
            cts=m.constraints.getChild(0).getChildren();
        }
        else {
            cts=m.constraints.getChildren();  // just one constraint inside the Top.
        }
        
        TreeTransformer sa=new SubstituteAllValues(solverSolution);
        
        TransformSimplify ts=new TransformSimplify();
        
        for(int i=0; i<cts.size(); i++) {
            ASTNode ct=cts.get(i).copy();
            
            ct=ts.transform(ct);  // This step may seem redundant but it deals with any variable name changes (by var unify) before the substitution. 
            ct=sa.transform(ct);
            ct=ts.transform(ct);
            
            if(! ((ct instanceof BooleanConstant) && ct.getValue()==1)) {
                CmdFlags.errorExit("When checking constraint: "+cts.get(i), "Constraint not satisfied by solver solution.", "Evaluation is:"+ct);
            }
        }
    }
    
}
