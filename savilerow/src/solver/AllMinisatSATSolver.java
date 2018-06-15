
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

//  Subclasses of SATSolver provide the runSatSolver method that returns a string
//  containing the solution literals and a stats object.

public class AllMinisatSATSolver extends SATSolver
{
    public AllMinisatSATSolver(Model _m) {
        super(_m);
    }

    //override from the parent
    public void findMultipleSolutions(String satSolverName, String fileName, Model m) {
        double srtime=(((double) System.currentTimeMillis() - CmdFlags.startTime) / 1000);
        CmdFlags.runningSolver=true;
        
        Stats totalstats=null;
        try{
          ArrayList<String> command = new ArrayList<String>();
          command.add(satSolverName);
          command.add(fileName);
          command.add(CmdFlags.getMinionSolsTempFile());
          
          ArrayList<String> stderr_lines=new ArrayList<String>();
          ArrayList<String> stdout_lines=new ArrayList<String>();
          
          ReadProcessOutput rpo=new ReadProcessOutput(stdout_lines);
          
          double solvertime=System.currentTimeMillis();
          
          int exitValue=RunCommand.runCommand(false, command, stderr_lines, rpo);
          
          solvertime=(((double) System.currentTimeMillis() - solvertime) / 1000);
          
          //  Back into SR -- store the time it restarted
          CmdFlags.startTime=System.currentTimeMillis();
          
          AllMinisatStats stats = new AllMinisatStats(stdout_lines);
          
          if(exitValue==0) {
              // Non-Trivial problem
              BufferedReader inFromFile =new BufferedReader(new FileReader(CmdFlags.getMinionSolsTempFile()));
              while (inFromFile.ready())
              {
                  String currentSolutionString=inFromFile.readLine();
                  ArrayList<String> currentSolution = new ArrayList<String>(Arrays.asList(currentSolutionString.split(" ")));
                  Solution sol=solverSolToAST(currentSolution, m.global_symbols);
                  
                  createSolutionFile(sol, true);
              }
              stats.setNontrivialStats(solutionCounter);
          }
          else if(exitValue==20) {
              // Trivial.
              stats.setTrivialStats();
          }
          else if(stderr_lines.size()!=0 || (exitValue!=0 && exitValue!=20)) {
              CmdFlags.println("SAT solver exited with error code:"+exitValue+" and message:");
              CmdFlags.println(stderr_lines);
          }

          if(totalstats==null) {
              totalstats=stats;
          }
          else {
              totalstats=totalstats.add(stats);
          }
          
          //  Add on the time for parsing sols etc. 
          srtime += (((double) System.currentTimeMillis() - CmdFlags.startTime) / 1000);
          
          //  Reset the start time again. In mining mode this means the next block in the .info file will have the sr time needed to update the DIMACS file only. 
          CmdFlags.startTime=System.currentTimeMillis();
          
          totalstats.putValue("SavileRowTotalTime", String.valueOf(srtime));
          writeToFileSolutionStats(totalstats);
          CmdFlags.rmTempFiles();
        }
        catch(IOException e1) {
            System.err.println("IOException");
            e1.printStackTrace();
            CmdFlags.rmTempFiles();
        }
        catch(InterruptedException e2) {
            System.out.println("InterruptedException.");
            CmdFlags.rmTempFiles();
        }
    }

    //required to implement this method even though I dont use import junit.framework.TestCase;
    public Pair<ArrayList<String>, Stats> runSatSolver(String satSolverName, String filename, Model m, Stats statssofar) throws IOException,  InterruptedException
    {
      return new Pair<ArrayList<String>, Stats>(null, null);
    }
}
