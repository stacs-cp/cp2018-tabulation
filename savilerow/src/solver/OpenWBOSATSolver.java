
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

import savilerow.*;
import savilerow.model.*;
import savilerow.expression.*;
import savilerow.CmdFlags;
import savilerow.eprimeparser.EPrimeReader;

//  Subclasses of SATSolver provide the runSatSolver method that returns a string
//  containing the solution literals and a stats object. 

public class OpenWBOSATSolver extends SATSolver
{
    public OpenWBOSATSolver(Model _m) {
        super(_m);
    }
    public Pair<ArrayList<String>, Stats> runSatSolver(String satSolverName, String filename, Model m, Stats statssofar) throws IOException,  InterruptedException
    {
        CmdFlags.runningSolver=true;  // Prevents SR's timeout from kicking in. 
        
        try {
            ArrayList<String> command = new ArrayList<String>();
            command.add(satSolverName);
            
            ArrayList<String> extraflags=new ArrayList<String>(CmdFlags.getSolverExtraFlags());
            
            assert statssofar==null;  // Runs once. 
            
            command.addAll(extraflags);
            command.add(filename);
            
            ArrayList<String> stderr_lines=new ArrayList<String>();
            ArrayList<String> stdout_lines=new ArrayList<String>();
            
            ReadProcessOutput rpo=new ReadProcessOutput(stdout_lines);
            
            double solvertime=System.currentTimeMillis();
            
            int exitValue=RunCommand.runCommand(false, command, stderr_lines, rpo);
            
            if(exitValue!=20 && exitValue!=30) {
                //  30 means optimum found, 20 means unsat.
                CmdFlags.println("OpenWBO exited with error code:"+exitValue+" and error message:");
                CmdFlags.println(stderr_lines);
            }
            
            boolean completed=(exitValue==20 || exitValue==30);
            boolean satisfiable=(exitValue==30);
            
            solvertime=(((double) System.currentTimeMillis() - solvertime) / 1000);
            
            Stats stats=new OpenWBOStats(stdout_lines);
            stats.putValue("SolverTotalTime", String.valueOf(solvertime));
            
            if(satisfiable) {
                ArrayList<String> fileContents=new ArrayList<String>();
                
                for(int i=0; i<stdout_lines.size(); i++) {
                    String ln=stdout_lines.get(i);
                    if(ln.indexOf("v ")==0) {
                        String[] words=ln.trim().split(" ");
                        fileContents.addAll(Arrays.asList(words).subList(1, words.length));   // Leave the starting v
                    }
                }
                
                return new Pair<ArrayList<String>, Stats>(fileContents, stats);
            }
            else {
                // Either unsat or not completed
                return new Pair<ArrayList<String>, Stats>(null, stats);
            }
        }
        catch(Exception e) {
            System.out.println("Exception."+e);
            CmdFlags.rmTempFiles();
            return new Pair<ArrayList<String>, Stats>(null, null);
        }
    }
}
