package savilerow.solver;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2017 Patrick Spracklen and Peter Nightingale
    
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

import savilerow.*;
import savilerow.model.*;
import savilerow.expression.*;
import savilerow.CmdFlags;
import savilerow.eprimeparser.EPrimeReader;

public abstract class SATSolver extends Solver
{
    static int solutionNumber=1;
    private ArrayList<String> stdout_lines=new ArrayList<String>();
    
    Model m;
    public SATSolver(Model _m) {
        m=_m;
    }
    
    // satSolverName is the name of the SAT solver binary
    // filename is the name of the CNF file. 
    // m is the model 
    public void findSolutions(String satSolverName, String fileName, Model m) throws IOException,  InterruptedException
    {
        //If there is an objective (maximising/minimising)
        if (m.objective!=null) {
            findObjective(satSolverName,fileName, m);
        }
        
        //Check if all solutions are required
        else if(CmdFlags.getFindAllSolutions() || CmdFlags.getFindNumSolutions()>-1) {
            findMultipleSolutions(satSolverName,fileName,m);
        }
        else {
            findOneSolution(satSolverName, fileName, m);
        }
    }
    
    // Instantiated for different SAT solver classes. 
    public abstract Pair<ArrayList<String>, Stats> runSatSolver(String satSolverName, String filename, Model m, Stats statssofar) throws IOException,  InterruptedException;
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //   Private methods. 
    
    // Method which adds the negation of the current solution to the dimacs file. Used 
    // when multiple solutions are required.
    public void findMultipleSolutions(String satSolverName, String fileName, Model m) {
        double srtime=(((double) System.currentTimeMillis() - CmdFlags.startTime) / 1000);
        
        int numdigits=6;
        
        try{
            Stats totalstats=null;
            
            while(true)
            {
                if( !(CmdFlags.getFindAllSolutions()) && solutionCounter>=CmdFlags.getFindNumSolutions()) {
                    // Finished.
                    break;
                }
                
                Pair<ArrayList<String>, Stats> p=runSatSolver(satSolverName,fileName, m, totalstats);
                
                ArrayList<String> currentSolution=p.getFirst();
                Stats stats=p.getSecond();
                
                if(totalstats==null) {
                    totalstats=stats;
                }
                else {
                    totalstats=totalstats.add(stats);
                }
                
                if(currentSolution==null) {
                    break;
                }
                
                Solution sol=solverSolToAST(currentSolution, m.global_symbols);
                
                createSolutionFile(sol, true);
                
                // Iterate through the solution as assignments to SR variables
                // and use the negation of the direct encoding of each assignment.
                ArrayList<Long> clauseToAdd=new ArrayList<Long>();
                HashMap<String, Long> collect_all_values=readAllAssignments(currentSolution, m.global_symbols);   // Collect the value of every variable,
                for (Map.Entry<String, Long> entry : collect_all_values.entrySet()) {
                    String key = entry.getKey();
                    Long value = entry.getValue();
                    ASTNode var=new Identifier(m, key);
                    if(m.global_symbols.category.get(key).cat!=ASTNode.Auxiliary) {
                        long lit=-var.directEncode(m.satModel, value);
                        if(lit==1) {
                            //  There is no direct encoding of this var/val pair. Must be that the variable has no direct encoding. Use the order encoding.
                            //  Either less than or greater than the val.
                            clauseToAdd.add(var.orderEncode(m.satModel, value-1));
                            clauseToAdd.add(-var.orderEncode(m.satModel, value));
                        }
                        else {
                            clauseToAdd.add(lit);
                        }
                    }
                }
                
                m.satModel.addClauseAfterFinalise(clauseToAdd);
            }
            totalstats.putValue("SavileRowTotalTime", String.valueOf(srtime));
            writeToFileSolutionStats(totalstats);
        }
        catch(Exception e) {
            e.printStackTrace();
        }
    }
    
    // Method to find an objective (minimising/maximising problem)
    public void findObjective(String satSolverName, String fileName, Model m) {
        if(CmdFlags.getMaxsattrans()) {
            findOneSolution(satSolverName, fileName, m);
        }
        else if(CmdFlags.getOptStrategy().equals("linear")) {
            findObjectiveLinear(satSolverName, fileName, m);
        }
        else if(CmdFlags.getOptStrategy().equals("unsat")) {
            findObjectiveUnsatMethod(satSolverName, fileName, m);
        }
        else {
            assert CmdFlags.getOptStrategy().equals("bisect");
            findObjectiveBisect(satSolverName, fileName, m);
        }
    }
    
    //  Find a solution, bound the objective, find another solution until unsat. 
    public void findObjectiveLinear(String satSolverName, String fileName, Model m)
    {
        double srtime=(((double) System.currentTimeMillis() - CmdFlags.startTime) / 1000);
        
        //Get the ASTNode that is constrained by the objective
        Identifier objectiveNode=(Identifier) m.objective.getChild(0);
        //Get the domain of the objective variable
        ArrayList<Intpair> domain=m.global_symbols.getDomain(objectiveNode.getName()).getIntervalSet();
        
        ArrayList<String> currentSolution=null;
        int solutionNumber=0;
        
        Stats totalstats=null;
        
        try {
            while(true) {
                Pair<ArrayList<String>, Stats> p=runSatSolver(satSolverName,fileName, m, totalstats);
                
                if(p.getFirst()!=null) currentSolution=p.getFirst();
                Stats stats=p.getSecond();
                
                if(totalstats==null) {
                    totalstats=stats;
                }
                else {
                    totalstats=totalstats.add(stats);
                }
                
                if(p.getFirst()==null) {
                    break;
                }
                
                // Get the assignments to SR variables.
                HashMap<String, Long> sol=readAllAssignments(currentSolution, m.global_symbols);
                
                Long objectiveValue=sol.get(m.objective.getChild(0).toString());
                
                System.out.println("While optimising, found value: "+objectiveValue);
                
                // Construct the new clause.
                if (m.objective instanceof Minimising) {
                    m.satModel.addClauseAfterFinalise(m.satModel.getOrderVariable(objectiveNode.getName(), objectiveValue-1));
                }
                else {
                    m.satModel.addClauseAfterFinalise(-m.satModel.getOrderVariable(objectiveNode.getName(), objectiveValue));
                }
                
                solutionNumber++;
            }
            
            if(solutionNumber>0)
            {
                Solution sol=solverSolToAST(currentSolution, m.global_symbols);
                
                createSolutionFile(sol, false);
            }
            else if(m.incumbentSolution!=null) {
                createSolutionFile(m.incumbentSolution, false);
            }
            totalstats.putValue("SavileRowTotalTime", String.valueOf(srtime));
            writeToFileSolutionStats(totalstats);
        }
        catch (Exception e)
        {
            e.printStackTrace();
        }
    }
    
    //  Start at the best value (lowest value for minimisation problems), assign it and attempt to find a solution. Iterate up through the domain. 
    public void findObjectiveUnsatMethod(String satSolverName, String fileName, Model m)
    {
        double srtime=(((double) System.currentTimeMillis() - CmdFlags.startTime) / 1000);
        
        //Get the ASTNode that is constrained by the objective
        Identifier objectiveNode=(Identifier) m.objective.getChild(0);
        //Get the domain of the objective variable
        ArrayList<Intpair> domain=m.global_symbols.getDomain(objectiveNode.getName()).getIntervalSet();
        
        ArrayList<String> currentSolution=null;
        int solutionNumber=0;
        
        Stats totalstats=null;
        
        try {
            if (m.objective instanceof Minimising) {
                // Iterate in ascending order.
                for(int i=0; i<domain.size(); i++) {
                    for(long j=domain.get(i).lower; j<=domain.get(i).upper; j++) {
                        Pair<Stats, ArrayList<String>> p=optTestValue(satSolverName, fileName, objectiveNode, j, totalstats);
                        totalstats=p.getFirst();
                        currentSolution=p.getSecond();
                        if(currentSolution!=null) {
                            break;
                        }
                    }
                    if(currentSolution!=null) {
                        break;
                    }
                }
            }
            else {
                // Iterate in descending order.
                for(int i=domain.size()-1; i>=0; i--) {
                    for(long j=domain.get(i).upper; j>=domain.get(i).lower; j--) {
                        Pair<Stats, ArrayList<String>> p=optTestValue(satSolverName, fileName, objectiveNode, j, totalstats);
                        totalstats=p.getFirst();
                        currentSolution=p.getSecond();
                        if(currentSolution!=null) {
                            break;
                        }
                    }
                    if(currentSolution!=null) {
                        break;
                    }
                }
            }
            
            // Get the assignments to SR variables.
            if(currentSolution!=null) {
                HashMap<String, Long> sol=readAllAssignments(currentSolution, m.global_symbols);
                
                Long objectiveValue=sol.get(m.objective.getChild(0).toString());
                
                System.out.println("While optimising, found value: "+objectiveValue);
                
                Solution solast=solverSolToAST(currentSolution, m.global_symbols);
                
                createSolutionFile(solast, false);
            }
            else if(m.incumbentSolution!=null) {
                createSolutionFile(m.incumbentSolution, false);
            }
            
            totalstats.putValue("SavileRowTotalTime", String.valueOf(srtime));
            writeToFileSolutionStats(totalstats);
        }
        catch (Exception e)
        {
            e.printStackTrace();
        }
    }
    
    private Pair<Stats, ArrayList<String>> optTestValue(String satSolverName, String fileName, ASTNode objectiveNode, long val, Stats totalstats) throws IOException, InterruptedException {
        System.out.println("Testing value: "+val);
        m.satModel.addClauseAfterFinalise(objectiveNode.orderEncode(m.satModel, val));
        m.satModel.addClauseAfterFinalise(-objectiveNode.orderEncode(m.satModel, val-1));
        
        Pair<ArrayList<String>, Stats> p=runSatSolver(satSolverName,fileName, m, totalstats);
        m.satModel.removeFinalClause();
        m.satModel.removeFinalClause();
        
        //System.out.println(p);
        ArrayList<String> currentSolution=null;
        if(p.getFirst()!=null) currentSolution=p.getFirst();
        
        Stats stats=p.getSecond();
        
        if(totalstats==null) {
            totalstats=stats;
        }
        else {
            totalstats=totalstats.add(stats);
        }
        return new Pair<Stats, ArrayList<String>>(totalstats, currentSolution);
    }
    
    //  Dichotomic search for the optimal solution.  
    public void findObjectiveBisect(String satSolverName, String fileName, Model m)
    {
        double srtime=(((double) System.currentTimeMillis() - CmdFlags.startTime) / 1000);
        
        //Get the ASTNode that is constrained by the objective
        Identifier objectiveNode=(Identifier) m.objective.getChild(0);
        //Get the domain of the objective variable
        ArrayList<Intpair> domain=m.global_symbols.getDomain(objectiveNode.getName()).getIntervalSet();
        
        ArrayList<String> currentSolution=null;
        int solutionNumber=0;
        
        Stats totalstats=null;
        
        
        try {
            long lower=domain.get(0).lower;
            long upper=domain.get(domain.size()-1).upper;
            
            //  First search with no constraint on the objective. 
            System.out.println("In dichotomic search, lower: "+lower+" upper: "+upper);
            
            Pair<ArrayList<String>, Stats> p=runSatSolver(satSolverName,fileName, m, totalstats);
            
            if(p.getFirst()!=null) currentSolution=p.getFirst();
            totalstats=p.getSecond();
            if(p.getFirst()==null) {
                // No solution
                if(m.incumbentSolution!=null) {
                    createSolutionFile(m.incumbentSolution, false);
                }
                totalstats.putValue("SavileRowTotalTime", String.valueOf(srtime));
                writeToFileSolutionStats(totalstats);
                return;
            }
            else {
                // A solution was found. 
                // Get the assignments to SR variables.
                HashMap<String, Long> sol=readAllAssignments(currentSolution, m.global_symbols);
                
                Long objectiveValue=sol.get(m.objective.getChild(0).toString());
                
                System.out.println("While optimising, found value: "+objectiveValue);
                
                solutionNumber++;
                
                // We have a new upper bound (minimising) or lower bound (maximising)
                if (m.objective instanceof Minimising) {
                    upper=objectiveValue-1;
                }
                else {
                    lower=objectiveValue+1;
                }
            }
            
            boolean done=false;
            while(!done) {
                // Midpoint.
                long mid=(upper-lower+1)/2+lower;
                System.out.println("In dichotomic search, lower: "+lower+" upper: "+upper+" midpoint: "+mid);
                // Add the clause opt<=mid or opt>=mid
                // Construct the new clause.
                if (m.objective instanceof Minimising) {
                    m.satModel.addClauseAfterFinalise(m.satModel.getOrderVariable(objectiveNode.getName(), mid));
                }
                else {
                    m.satModel.addClauseAfterFinalise(-m.satModel.getOrderVariable(objectiveNode.getName(), mid-1));
                }
                
                p=runSatSolver(satSolverName,fileName, m, totalstats);
                
                if(p.getFirst()!=null) currentSolution=p.getFirst();
                Stats stats=p.getSecond();
                
                totalstats=totalstats.add(stats);
                
                if(p.getFirst()==null) {
                    // We have a new lower bound (minimising) or upper bound (maximising)
                    if (m.objective instanceof Minimising) {
                        lower=mid+1;
                    }
                    else {
                        upper=mid-1;
                    }
                }
                else {
                    // A solution was found. 
                    // Get the assignments to SR variables.
                    HashMap<String, Long> sol=readAllAssignments(currentSolution, m.global_symbols);
                    
                    Long objectiveValue=sol.get(m.objective.getChild(0).toString());
                    
                    System.out.println("While optimising, found value: "+objectiveValue);
                    
                    solutionNumber++;
                    
                    // We have a new upper bound (minimising) or lower bound (maximising)
                    if (m.objective instanceof Minimising) {
                        upper=objectiveValue-1;
                    }
                    else {
                        lower=objectiveValue+1;
                    }
                }
                
                //  Retract the mid-point clause
                m.satModel.removeFinalClause();
                //  Permanently bound the search within lower..upper
                m.satModel.addClauseAfterFinalise(m.satModel.getOrderVariable(objectiveNode.getName(), upper));
                m.satModel.addClauseAfterFinalise(-m.satModel.getOrderVariable(objectiveNode.getName(), lower-1));
                
                if(lower>upper) {
                    break;
                }
            }
            
            if(solutionNumber>0)
            {
                Solution sol=solverSolToAST(currentSolution, m.global_symbols);
                
                createSolutionFile(sol, false);
            }
            else if(m.incumbentSolution!=null) {
                createSolutionFile(m.incumbentSolution, false);
            }
            totalstats.putValue("SavileRowTotalTime", String.valueOf(srtime));
            writeToFileSolutionStats(totalstats);
        }
        catch (Exception e)
        {
            e.printStackTrace();
        }
    }
    
    // Find a single solution, if there is one. 
    public void findOneSolution(String satSolverName, String fileName, Model m)
    {
        double srtime=(((double) System.currentTimeMillis() - CmdFlags.startTime) / 1000);
        
        try {
            Pair<ArrayList<String>, Stats> p=runSatSolver(satSolverName,fileName, m, null);
            
            ArrayList<String> currentSolution=p.getFirst();
            Stats stats=p.getSecond();
            stats.putValue("SavileRowTotalTime", String.valueOf(srtime));
            
            writeToFileSolutionStats(stats);
            
            //Get the assignment of variables returned by the sat solver.
            if(currentSolution!=null) {
                Solution sol=solverSolToAST(currentSolution, m.global_symbols);
                createSolutionFile(sol, false);
            }
            else if(m.incumbentSolution!=null) {   // In a case where the objective was dropped. 
                createSolutionFile(m.incumbentSolution, false);
            }
            else {
                System.out.println("No solution found.");
            }
            
            CmdFlags.rmTempFiles();
        }
        catch (Exception e)
        {
            e.printStackTrace();
        }
    }
    
    // To be used when parsing all/multiple solutions.
    Solution parseOneSolverSolution(SymbolTable st, BufferedReader in) {
        return null;
    }
    
    Solution parseLastSolverSolution(SymbolTable st, BufferedReader in) {
        return null;
    }
    
    protected void writeToFileSolutionStats(Stats stats) {
        // Add the number of SAT variables and SAT clauses.
        stats.putValue("SATVars", String.valueOf(m.satModel.getNumVars()));
        stats.putValue("SATClauses", String.valueOf(m.satModel.getNumClauses()));
        
        // Create .info and .infor files. 
        if(stats!=null) {
            stats.makeInfoFiles();
        }
    }
    
    
    
    // Takes a solution as SAT literals
    // and turns it into a hashmap mapping variable name to value.
    HashMap<String, Long> readAllAssignments(ArrayList<String> satSol, SymbolTable st) {
        HashMap<String, Long> collect_all_values=new HashMap<String, Long>();
        
        Sat satModel=st.m.satModel;
        
        long assignprev=0;
        for(int i=0; i<satSol.size(); i++) {
            long assign=Long.valueOf(satSol.get(i));
            
            //  Direct encoding
            NumberMap n = satModel.getDimacsMapping(assign);
            
            if(n!=null) {
                collect_all_values.put(n.getVariable(), n.getValue());
                assignprev=assign;
                continue;
            }
            
            // Order encoding -- for variables that have only order encoding.
            // Solvers MUST output literals in order for this to work. 
            
            // There are three cases. For the first var in the order enc, i.e. [x<=min(D(x))], 
            // if the literal is positive we find it in orderMappingMin to get the SR variable and value.
            
            if(assign>0) {
                n=satModel.orderMappingMin.get(assign);
                if(n!=null) {
                    collect_all_values.put(n.getVariable(), n.getValue());
                    assignprev=assign;
                    continue;
                }
            }
            
            // For other vars in the order enc, if the var is positive and its
            // predecessor is negative, then we can find it in orderMappingMid.
            
            if(assign>0 && assignprev<0) {
                n=satModel.orderMappingMid.get(assign);
                if(n!=null) {
                    collect_all_values.put(n.getVariable(), n.getValue());
                    assignprev=assign;
                    continue;
                }
            }
            
            // For the top value in the domain, there is no [x<=max(D(x))] SAT variable
            // The topmost SAT variable must be false in this case so we use that.
            
            if(assign<0) {
                n=satModel.orderMappingMax.get(assign);
                if(n!=null) {
                    collect_all_values.put(n.getVariable(), n.getValue());
                    assignprev=assign;
                    continue;
                }
            }
            
            assignprev=assign;  // Store for next iteration
        }
        
        // Bit of a hack -- should be somewhere else.
        if(CmdFlags.getTestSolutions()) {
            checkSolution(collect_all_values);
        }
        
        return collect_all_values;
    }
}
