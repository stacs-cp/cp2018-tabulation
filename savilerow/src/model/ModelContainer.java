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

import savilerow.expression.*;
import savilerow.treetransformer.*;
import savilerow.eprimeparser.EPrimeReader;
import savilerow.model.*;
import savilerow.solver.*;
import savilerow.*;

import java.util.*;
import java.io.*;

// This class controls the refinement process.

public class ModelContainer {
    
    public Model m;
    public ArrayList<ASTNode> parameters;
    
    public ModelContainer(Model _m, ArrayList<ASTNode> _parameters) {
        m = _m;
        parameters = _parameters;
    }
    
    public void process() {
        processPreamble();
        
        if (CmdFlags.getDominiontrans()) {
            classLevelFlattening();
        } else {
            instancePreFlattening1();
            
            if (CmdFlags.getUsePropagate()) {
                squashDomains();
                CmdFlags.currentModel=m;
            }
            
            instancePreFlattening2(false);
            
            if (CmdFlags.getMode() == CmdFlags.Multi) {
                branchingInstanceFlattening();
            } else {
                instanceFlattening(-1, false);                // no model number.
                postFlattening(-1, false);
            }
        }
    }
    
    // Same as process except does not run solver at the end.
    // This is to get the JVM up to speed.
    public void dryrun() {
        processPreamble();
        
        if (CmdFlags.getDominiontrans()) {
            classLevelFlattening();
        } else {
            instancePreFlattening1();
            
            if (CmdFlags.getUsePropagate()) {
                squashDomains();
                CmdFlags.currentModel=m;
            }
            
            instancePreFlattening2(false);
            
            if (CmdFlags.getMode() == CmdFlags.Multi) {
                branchingInstanceFlattening();
            } else {
                instanceFlattening(-1, false);                // no model number.
                // postFlattening(-1, false);
            }
        }
    }
    
    public void processPreamble() {
        CmdFlags.setOutputReady(false);        // Make sure we are not in 'output ready' state.
        CmdFlags.setAfterAggregate(false);
        ////////////////////////////////////////////////////////////////////////////
        // Substitute in the parameters
        
        // Process lettings, givens, wheres, and finds in order of declaration.
        ArrayDeque<ASTNode> preamble = m.global_symbols.lettings_givens;

        // The next loop will pull things out of the parameter file, so first
        // deal with the parameters -- make undef safe, simplify.
        for (int i =0; i < parameters.size(); i++) {
            ASTNode a = parameters.get(i);

            if (!a.typecheck(m.global_symbols)) {
                CmdFlags.errorExit("Failed type checking in parameter file:" + a);
            }

            TransformMakeSafe tms = new TransformMakeSafe(m);
            a = tms.transform(a);

            // Extract any extra constraints that were generated and add them to the end of the
            // preamble in a Where statement.
            ASTNode extra_cts = tms.getContextCts();
            if (extra_cts != null) {
                preamble.addLast(new Where(extra_cts));                /// What if the parameter is not used?
            }

            TransformSimplify ts = new TransformSimplify();
            a = ts.transform(a);

            // Unroll and evaluate any matrix comprehensions or quantifiers in the parameters.
            TransformQuantifiedExpression t2 = new TransformQuantifiedExpression(m);
            a = t2.transform(a);

            a = ts.transform(a);

            a = fixIndexDomainsLetting(a);            // Repair any inconsistency between the indices in a matrix and its matrix domain (if there is one).

            parameters.set(i, a);

            // Scan forward in the parameters to sub this parameter into future ones.
            ReplaceASTNode rep = new ReplaceASTNode(a.getChild(0), a.getChild(1));
            for (int j = i + 1; j < parameters.size(); j++) {
                parameters.set(j, rep.transform(parameters.get(j)));
            }
        }

        // Now go through the preamble in order.
        while (preamble.size() != 0) {
            ASTNode a = preamble.removeFirst();
            
            // Type check, deal with partial functions, simplify
            if (!a.typecheck(m.global_symbols)) {
                CmdFlags.errorExit("Failed type checking:" + a);
            }
            
            TransformMakeSafe tms = new TransformMakeSafe(m);
            a = tms.transform(a);
            
            // Extract any extra constraints generated in TransformMakeSafe.
            ASTNode extra_cts = tms.getContextCts();
            if (extra_cts != null) {
                preamble.addLast(new Where(extra_cts));
            }
            
            TransformSimplify ts = new TransformSimplify();
            a = ts.transform(a);
            
            // Process any quantifiers before simplifying again.
            if (!CmdFlags.getDominiontrans()) {
                TransformQuantifiedExpression t2 = new TransformQuantifiedExpression(m);
                a = t2.transform(a);
            }
            a = ts.transform(a);
            
            if (a instanceof Letting) {
                a=fixIndexDomainsLetting(a);                // Repair any inconsistency between the indices in a matrix and its matrix domain (if there is one).
                processLetting(a);
            } else if (a instanceof Find) {
                processFind(a);
            } else if (a instanceof Where) {
                processWhere(a);
            } else {
                assert a instanceof Given;
                processGiven(a);
            }
        }
        
        if (parameters.size() > 0) {
            CmdFlags.warning("Number of givens in model file does not match number of lettings in parameter file.");
        }
        
        parameters = null;        // No longer needed.
        
        // Run type-checker before any transformation.
        if (!m.typecheck()) {
            CmdFlags.errorExit("Failed type checking after substituting in lettings.");
        }
        if(CmdFlags.getVerbose()) {
            CmdFlags.println("Model before undef handling:");
            CmdFlags.println(m);
        }
        
        //  Remove matrices indexed by matrices. 
        removeMatrixIndexedMatrices();
        
        // Deal with partial functions in the constraints/objective/branchingOn
        TransformMakeSafe tms = new TransformMakeSafe(m);
        m.transform(tms);

        // Make sure constant folding is done before the next rule.
        m.simplify();
    }

    ////////////////////////////////////////////////////////////////////////
    //
    // Non-class-level transformations (to Minion/Gecode/Minizinc/SAT)

    public void instancePreFlattening1() {
        if( (! CmdFlags.getMinionSNStrans()) && m.sns!=null) {
            //  If the output solver is not Minion SNS, deactivate the neighbourhood constraints early (before TQE)
            ASTNode newcons=((SNS)m.sns).deactivateEarly();
            m.constraints.getChild(0).setParent(null); // Do not copy the constraint set.
            m.constraints.setChild(0, new And(m.constraints.getChild(0), newcons));
            m.simplify();
        }
        
        //TransformMakeTableEarly tmte=new TransformMakeTableEarly(m);   //  Attempt to deal with makeTable functions before unrolling quantifiers.
        //m.transform(tmte);
        
        TransformQuantifiedExpression t2 = new TransformQuantifiedExpression(m);
        m.transform(t2);
        
        //  TransformMatrixIndices must be done before TransformMatrixDeref.
        //  No longer -- shift to transform to element constraint will occur later.
        /*HashMap<String, ASTNode> doms = m.global_symbols.getDomains();
        Iterator<Map.Entry<String, ASTNode>> itr = doms.entrySet().iterator();
        while (itr.hasNext()) {
            Map.Entry<String, ASTNode> a = itr.next();
            if (a.getValue() instanceof MatrixDomain) {

                TransformMatrixIndices ti = new TransformMatrixIndices(0, m, a.getKey());
                m.transform(ti);
            }
        }
        CmdFlags.tick("done TransformMatrixIndices");*/
        
        ////////////////////////////////////////////////////////////////////////
        //
        // Atomise matrices of variables.
        destroyMatrices();
        
        //  Structured Neighbourhood Search
        if(m.sns!=null) {
            // Generate the bool and constraints to disable the incumbent variables
            ASTNode newcons=((SNSIncumbentMapping)m.sns.getChild(0)).makeIncumbentDisable();
            m.constraints.getChild(0).setParent(null);  // Do not copy the constraint set.
            m.constraints.setChild(0, new And(m.constraints.getChild(0), newcons));
            m.simplify();
        }
        
        ////////////////////////////////////////////////////////////////////////
        //
        // Create element functions from matrix derefs.
        
        TransformMatrixDeref t3 = new TransformMatrixDeref(m);
        m.transform(t3);
        
        ////////////////////////////////////////////////////////////////////////
        // Symmetry detection and breaking
        
        if(CmdFlags.getGraphColSymBreak()) {
            //  Highly specific value symmetry breaking for graph colouring.
            TransformGCAssignClique gc=new TransformGCAssignClique(m);
            m.transform(gc);
        }
        
        if(CmdFlags.getUseVarSymBreaking()) {
            writeModelAsJSON(m);
        }
        
        ////////////////////////////////////////////////////////////////////////
        //
        // If objective function is not a solitary variable, do one flattening op on it.

        if (m.objective != null) {
            ASTNode ob = m.objective.getChild(0);
            if (!ob.isConstant() && ! (ob instanceof Identifier)) {
                boolean flatten = true;
                if (ob instanceof MatrixDeref || ob instanceof SafeMatrixDeref) {
                    flatten = false;
                    for (int i =1; i < ob.numChildren(); i++) {
                        if (! ob.getChild(i).isConstant()) {
                            flatten = true;
                        }
                    }
                }
                
                if (flatten) {
                    ASTNode auxvar = m.global_symbols.newAuxHelper(ob);
                    ASTNode flatcon = new ToVariable(ob, auxvar);
                    m.global_symbols.auxVarRepresentsConstraint(auxvar.toString(), ob.toString());
                    m.objective.setChild(0, auxvar);
                    m.constraints.getChild(0).setParent(null);   //  Do not copy the constraint set.
                    m.constraints.setChild(0, new And(flatcon, m.constraints.getChild(0)));
                }
            }
        }
        
        // Put into normal form.
        TransformNormalise tn = new TransformNormalise(m);
        m.transform(tn);
    }

    public void instancePreFlattening2(boolean propagate) {
        ////////////////////////////////////////////////////////////////////////
        // Pre-flattening rearrangement
        
        if( (! CmdFlags.getMinionSNStrans() || propagate) && m.sns!=null) {
            //  If the output solver is not Minion SNS, remove the neighbourhood constraints, incumbent variables etc.
            ASTNode newcons=((SNS)m.sns).deactivate();
            m.constraints.getChild(0).setParent(null); // Do not copy the constraint set.
            m.constraints.setChild(0, new And(m.constraints.getChild(0), newcons));
            m.simplify();
            
            // Throw away the SNS object.
            m.sns=null;
        }
        
        // Delete redundant variables.
        if (CmdFlags.getRemoveRedundantVars()) {
            RemoveRedundantVars rrv=new RemoveRedundantVars();
            rrv.transform(m);
        }
        
        ////////////////////////////////////////////////////////////////////////
        //
        // Aggregation
        // Just Alldiff and GCC at the moment.
        
        if (CmdFlags.getUseAggregate()) {
            TransformCollectAlldiff tca = new TransformCollectAlldiff(m);
            m.transform(tca);
            
            TransformCollectGCC tcg = new TransformCollectGCC(m);
            m.transform(tcg);
        }
        CmdFlags.setAfterAggregate(true);
        
        if(CmdFlags.getUseDeleteVars() && CmdFlags.getUseAggregate()) {
            m.simplify();  // Delete vars is switched on after aggregation. 
        }
        
        TransformAlldiffExcept tae = new TransformAlldiffExcept(m);
        m.transform(tae);
        
        TransformOccurrence t35 = new TransformOccurrence();
        m.transform(t35);
        
        if (CmdFlags.getUseBoundVars() && CmdFlags.getMiniontrans()) {
            // Weird things to deal with Minion and BOUND variables.
            TransformForBoundVars t36 = new TransformForBoundVars(m);
            m.transform(t36);
        }
        
        // if two sums are equal, rearrange to one sum=0.
        // TransformSumEqualSum tses=new TransformSumEqualSum(m);
        // m.transform(tses);
        
        // boolvar=1 ==> boolvar,  boolvar=0 ==> not(boolvar).
        TransformBoolEq tbe = new TransformBoolEq(m);
        m.transform(tbe);
        
        ////////////////////////////////////////////////////////////////////////
        //
        // Add pre-flattening implied constraints.
        
        // Add implied sum constraint on card variables based on GCC.
        TransformGCCSum tgs = new TransformGCCSum(m);
        m.transform(tgs);
        
        ////////////////////////////////////////////////////////////////////////
        // Other pre-flattening optimisations
        TransformMakeTable tmt=new TransformMakeTable(m, propagate);
        
        if(!propagate && (CmdFlags.make_short_tab==3 || CmdFlags.make_short_tab==4)) {
            TransformNormalise tn=new TransformNormalise(m);  //  Normalise to remove any duplicate constraints that would trigger identical scopes heuristic.
            m.transform(tn);
            
            TransformMakeTableScopes tmts=new TransformMakeTableScopes(m, tmt);
            
            m.transform(tmts);    //  Scan for identical scopes
            tmts.doIt();          //  Tabulate sets of constraints on identical scopes.
        }
        
        m.transform(tmt);
        
        TransformLexAlldiff tla=new TransformLexAlldiff(m);
        m.transform(tla);
        
        ////////////////////////////////////////////////////////////////////////
        //
        // If we are generating Gecode output, decompose some reified constraints
        // Do this before flattening.
        if((CmdFlags.getGecodetrans() || CmdFlags.getChuffedtrans()) && !propagate) {
            TransformReifyAlldiff tgo1 = new TransformReifyAlldiff(m);
            m.transform(tgo1);
            
            TransformDecomposeNegativeTable tnt=new TransformDecomposeNegativeTable(m);
            m.transform(tnt);
            // More needed here.
        }
        
        if(CmdFlags.getChuffedtrans() && !propagate) {
            // Decompose AtLeast and AtMost constraints as in Chuffed's mznlib.
            TransformOccurrenceToSum tots=new TransformOccurrenceToSum();
            m.transform(tots);
            
            //  Same for GCC
            TransformGCCToSums tgts=new TransformGCCToSums();
            m.transform(tgts);
        }
        
        if(CmdFlags.getSattrans() && !propagate) {
            //  Use mappers to avoid unnecessary aux variables when targeting SAT. 
            TransformSumToShift tsts = new TransformSumToShift(m);
            m.transform(tsts);
            
            TransformProductToMult tptm = new TransformProductToMult(m);
            m.transform(tptm);
        }
        
        // Some reformulations will be affected by order, so normalise.
        TransformNormalise tnr = new TransformNormalise(m);
        m.transform(tnr);
        
    }

    // can be executed after instancePreFlattening1
    public void squashDomains() {
        Model ipf1 = m.copy();        // Take a copy of the model
        
        boolean tmp_outready = CmdFlags.getOutputReady();
        boolean tmp_afteragg = CmdFlags.getAfterAggregate();
        
        instancePreFlattening2(true);
        instanceFlattening(-1, true);
        ArrayList<ASTNode> newfinds = postFlattening(-1, true);
        
        // Rescue the FilteredDomainStore object, containing mappings from expressions to aux var names 
        FilteredDomainStore filt=m.filt;
        ASTNode isol=m.incumbentSolution;
        
        // Restore the model.
        m = ipf1;
        
        // Restore the FilteredDomainStore object. 
        m.filt=filt;
        m.incumbentSolution=isol;
        
        // Restore the control flags to their original state (flags should probably eventually be in the model.)
        CmdFlags.setOutputReady(tmp_outready);
        CmdFlags.setAfterAggregate(tmp_afteragg);
        
        // Apply reduced domains in newfinds to the symbol table.
        for (int i =0; i < newfinds.size(); i++) {
            ASTNode id = newfinds.get(i).getChild(0);
            ASTNode dom = newfinds.get(i).getChild(1);
            assert id instanceof Identifier;
            assert dom.isFiniteSet();
            
            String idname = id.toString();
            
            if (m.global_symbols.getCategory(idname) == ASTNode.Decision) {
                ASTNode olddom = m.global_symbols.getDomain(idname);
                ASTNode newdom = new Intersect(olddom, dom);
                
                // Intersect correctly casts a boolean set to a non-boolean set when
                // intersecting it with a set of int. Sort out the boolean case.
                // This is a rather unpleasant hack.
                if (olddom.isBooleanSet()) {
                    TransformSimplify ts = new TransformSimplify();
                    newdom = Intpair.makeDomain((ts.transform(newdom)).getIntervalSet(), true);
                }
                m.global_symbols.setDomain(idname, newdom);
            }
            else {
                // It is not a primary decision variable, it should be an aux variable. 
                // Store for use if the same aux var is made again. 
                
                m.filt.auxVarFilteredDomain(idname, dom);
            }
        }
        
        if(m.sns!=null && CmdFlags.getMinionSNStrans()) {
            //  Copy filtered domains over to incumbent variables as well as primary variables.
            ASTNode primaries=m.sns.getChild(0).getChild(0);
            ASTNode incumbents=m.sns.getChild(0).getChild(1);
            assert primaries instanceof CompoundMatrix;
            assert incumbents instanceof CompoundMatrix;
            
            for(int i=1; i<primaries.numChildren(); i++) {
                String primname=primaries.getChild(i).toString();
                String incumname=incumbents.getChild(i).toString();
                
                ASTNode primary_dom = m.global_symbols.getDomain(primname);
                ASTNode newdom = new Intersect(primary_dom, m.global_symbols.getDomain(incumname));
                
                // If the old domain of the incumbent was boolean, the replacement must be boolean.
                if (m.global_symbols.getDomain(incumname).isBooleanSet()) {
                    TransformSimplify ts = new TransformSimplify();
                    newdom = Intpair.makeDomain((ts.transform(newdom)).getIntervalSet(), true);
                }
                m.global_symbols.setDomain(incumname, newdom);
            }
        }
        
        m.simplify();        // Simplifies everything with the symbol table going before the constraints.
    }
    
    public void branchingInstanceFlattening() {
        CmdFlags.currentModel=null;   // For safety don't use the currentModel global. 
        
        // Make an array of transforms.
        ArrayList<TreeTransformer> tryout = new ArrayList<TreeTransformer>();
        
        // At the moment this order is significant.
        tryout.add(new TransformMultiplyOutSum());
        tryout.add(new TransformFactorOutSum());

        tryout.add(new TransformImplicationOr(false));
        tryout.add(new TransformImplicationOr(true));

        tryout.add(new TransformDeMorgans(true));
        tryout.add(new TransformDeMorgans(false));
        tryout.add(new TransformReverseDeMorgans(true));
        tryout.add(new TransformReverseDeMorgans(false));

        tryout.add(new TransformDistributeLogical(true, true));
        tryout.add(new TransformDistributeLogical(false, true));        // Blows up with plotting.
        tryout.add(new TransformFactorLogical(true));
        tryout.add(new TransformFactorLogical(false));

        ArrayList<ArrayList<Boolean>> switches_list = new ArrayList<ArrayList<Boolean>>();

        buildSwitches(switches_list, new ArrayList<Boolean>(), tryout.size());


        // Take a pristine copy before making any branches.
        Model mbackup = m.copy();

        int modelcount =0;

        for (int i =0; i < switches_list.size(); i++) {
            System.out.println("Switches: " + switches_list.get(i));

            boolean skip = false;            // skip this model.
            int skiploc = -1;

            for (int j =0; j < tryout.size(); j++) {
                if (switches_list.get(i).get(j)) {

                    String mod1 = m.toString();
                    boolean modelchanged = m.transform(tryout.get(j));
                    String mod2 = m.toString();

                    if (! modelchanged && ! mod1.equals(mod2)) {
                        CmdFlags.println("Yikes: modelchanged flag wrong.");
                        modelchanged = true;
                    }

                    if (!modelchanged) {
                        // One of the transformations did nothing. Skip this set of transformations,
                        // because there is another set where switches[j] is false.
                        skip = true;
                        skiploc = j;
                        break;
                    }
                }
            }

            if (!skip) {

                modelcount++;
                instanceFlattening(modelcount, false);
                postFlattening(modelcount, false);
            } else {
                assert skiploc > -1;

                // Move forward to next assignment where the prefix 0..skiploc is different.
                //

                while (i < switches_list.size() && switches_list.get(i).get(skiploc)) {
                    i++;
                }


                i--;                // to counteract the i++ in the main loop.
            }

            // Restore the model.
            m = mbackup.copy();

        }

        System.out.println("Total models:" + modelcount);


    }

    public void buildSwitches(ArrayList<ArrayList<Boolean>> switches_list, ArrayList<Boolean> switches, int numSwitches) {
        // numSwitches is the number left to fill in.
        if (numSwitches == 0) {
            switches_list.add(switches);
            return;
        }

        ArrayList<Boolean> false_copy_switches = new ArrayList<Boolean>(switches);
        false_copy_switches.add(false);

        ArrayList<Boolean> true_copy_switches = new ArrayList<Boolean>(switches);
        true_copy_switches.add(true);

        buildSwitches(switches_list, false_copy_switches, numSwitches - 1);
        buildSwitches(switches_list, true_copy_switches, numSwitches - 1);
    }


    // Model number is for when this is called by branchingInstanceFlattening
    // Propagate is for shrinking domains, and will return find statements for the
    // reduced domains.
    public void instanceFlattening(int modelnumber, boolean propagate) {
        
        ////////////////////////////////////////////////////////////////////////
        //
        // Special cases of flattening.
        
        ////////////////////////////////////////////////////////////////////////
        //
        // Variable elimination.
        
        if (CmdFlags.getUseEliminateVars() && !propagate) {
            /*for(int i=0; i<=50; i=i+10) {
                System.out.println("Eliminating vars with increase parameter of : "+i);
                VarElim v=new VarElim(m, i);
                v.eliminateVariables();
            }
            for(int i=2; i<=10; i++) {
                System.out.println("Eliminating vars with scale parameter of : "+i);
                VarElim v=new VarElim(m, 0, i);
                v.eliminateVariables();
            }
            // VarElim v=new VarElim(m, 20);
            VarElim v = new VarElim(m, true);
            v.eliminateVariables();*/
            
        }
        
        //  Undef handling for solvers that have no 'safe' constraints
        if((CmdFlags.getGecodetrans() || CmdFlags.getChuffedtrans() || CmdFlags.getMinizinctrans()) && !propagate) {
            TransformRemoveSafeTypes tfzn=new TransformRemoveSafeTypes(m);
            m.transform(tfzn);
        }
        
        if (CmdFlags.getVerbose()) {
            System.out.println("Rules: Normalisation and CSE");
        }
        
        //  Add implied sum constraints based on AllDiffs and GCCs. Only when using AC-CSE.
        TransformAlldiffGCCSum tags = new TransformAlldiffGCCSum(m);
        if(CmdFlags.getUseACCSE() || CmdFlags.getUseACCSEAlt()) {
            //  Note: when backend is Chuffed, already decomposed the GCC.  
            m.transform(tags);
        }
        
        // Sort expressions to help CSE.  This also helps with n-ary CSE by
        // sorting sub-expressions within the N-ary expression.
        TransformNormalise tnr = new TransformNormalise(m);
        
        // CSE in N-ary cts   --- *
        if (CmdFlags.getUseACCSE()) {
            m.transform(tnr);
            // Do N-ary * first.  Needs to be done before TransformTimes.
            // Unfortunately doing this early leads to possibility of making
            // an aux var, then finding (after some other CSEs) it is only used in one place.
            // Perhaps need a reverse flattening transform to deal with this.
            ACCSE c = new ACCSE();
            c.flattenCSEs(m, "*");
            CmdFlags.stats.put("AC-CSE-Times_number", c.numcse);
            CmdFlags.stats.put("AC-CSE-Times_eliminated_expressions", c.countcse);
            CmdFlags.stats.put("AC-CSE-Times_total_size", c.totallength);
            m.simplify();
            
            c.flattenCSEs(m, "xor");
            CmdFlags.stats.put("AC-CSE-Xor_number", c.numcse);
            CmdFlags.stats.put("AC-CSE-Xor_eliminated_expressions", c.countcse);
            CmdFlags.stats.put("AC-CSE-Xor_total_size", c.totallength);
            m.simplify();
        }
        
        if (CmdFlags.getUseACCSEAlt()) {
            // Araya, Trombettoni and Neveu algorithm.
            m.transform(tnr);            // Normalise again.

            ICSEProduct cp = new ICSEProduct();

            cp.flattenCSEs(m);
            m.simplify();
        }
        
        ////////////////////////////////////////////////////////////////////////
        //
        // Before flattening, deal with N-ary Times which can't appear in the output.
        // Needs to be done before plain CSE because it can cause  e.g.  ab  and abc
        // to have a standard CSE when N-ary CSE is switched off.
        CmdFlags.setOutputReady(true);
        
        TransformTimes ttimes = new TransformTimes(m);
        m.transform(ttimes);
        
        TransformXor txor = new TransformXor(m);
        m.transform(txor);
        
        // Plain CSE  -- Just top level constraints.
        if (CmdFlags.getUseCSE()) {
            m.transform(tnr);            // Normalise again. May not be necessary.
            
            CSETopLevel ctl = new CSETopLevel();
            ctl.flattenCSEs(m);
            CmdFlags.stats.put("CSETopLevel_number", ctl.numcse);
            CmdFlags.stats.put("CSETopLevel_eliminated_expressions", ctl.countcse);
            CmdFlags.stats.put("CSETopLevel_total_size", ctl.totallength);
            m.simplify();
        }
        
        // Subset N-ary CSE. Do this before plain CSE because otherwise NaryCSE
        // will only be able to take out subsets of aux variables.
        if (CmdFlags.getUseACCSE()) {
            ACCSE c = new ACCSE();
            
            m.transform(tnr);
            c.flattenCSEs(m, "\\/");
            CmdFlags.stats.put("AC-CSE-Or_number", c.numcse);
            CmdFlags.stats.put("AC-CSE-Or_eliminated_expressions", c.countcse);
            CmdFlags.stats.put("AC-CSE-Or_total_size", c.totallength);
            m.simplify();
            
            m.transform(tnr);
            c.flattenCSEs(m, "/\\");
            CmdFlags.stats.put("AC-CSE-And_number", c.numcse);
            CmdFlags.stats.put("AC-CSE-And_eliminated_expressions", c.countcse);
            CmdFlags.stats.put("AC-CSE-And_total_size", c.totallength);
            m.simplify();
            
            m.transform(tnr);
            
            if(CmdFlags.getUseActiveACCSE()) {
                ACCSEActiveSum c2=new ACCSEActiveSum();
                c2.flattenCSEs(m);
                CmdFlags.stats.put("Active-AC-CSE-Sum_number", c2.numcse);
                CmdFlags.stats.put("Active-AC-CSE-Sum_eliminated_expressions", c2.countcse);
                CmdFlags.stats.put("Active-AC-CSE-Sum_total_size", c2.totallength);
                CmdFlags.stats.put("Active-AC-CSE-Found", c2.active_ac_cs_found?1:0);
            }
            else if(CmdFlags.getUseActiveACCSE2()) {
                ACCSEActiveSum2 c2=new ACCSEActiveSum2();
                c2.flattenCSEs(m);
                CmdFlags.stats.put("Active-AC-CSE-Sum_number", c2.numcse);
                CmdFlags.stats.put("Active-AC-CSE-Sum_eliminated_expressions", c2.countcse);
                CmdFlags.stats.put("Active-AC-CSE-Sum_total_size", c2.totallength);
                CmdFlags.stats.put("Active-AC-CSE-Found", c2.active_ac_cs_found?1:0);
            }
            else {
                c.flattenCSEs(m, "+");
                CmdFlags.stats.put("AC-CSE-Sum_number", c.numcse);
                CmdFlags.stats.put("AC-CSE-Sum_eliminated_expressions", c.countcse);
                CmdFlags.stats.put("AC-CSE-Sum_total_size", c.totallength);
            }
        }
        
        if (CmdFlags.getUseACCSEAlt()) {
            //  Use X-CSE for disjunction and conjunction.
            ACCSE c = new ACCSE();
            
            m.transform(tnr);
            c.flattenCSEs(m, "\\/");
            CmdFlags.stats.put("AC-CSE-Or_number", c.numcse);
            CmdFlags.stats.put("AC-CSE-Or_eliminated_expressions", c.countcse);
            CmdFlags.stats.put("AC-CSE-Or_total_size", c.totallength);
            m.simplify();
            
            m.transform(tnr);
            c.flattenCSEs(m, "/\\");
            CmdFlags.stats.put("AC-CSE-And_number", c.numcse);
            CmdFlags.stats.put("AC-CSE-And_eliminated_expressions", c.countcse);
            CmdFlags.stats.put("AC-CSE-And_total_size", c.totallength);
            m.simplify();
            
            // Araya, Trombettoni and Neveu algorithm for sums only.
            m.transform(tnr);            // Normalise again.
            ICSESum c2 = new ICSESum();
            
            c2.flattenCSEs(m);
            m.simplify();
            
            // Doesn't do the stats yet.
        }
        
        ////////////////////////////////////////////////////////////////////////
        //
        // Remove redundant constraints that were added earlier, derived from AllDiff or GCC
        // if they were not modified by AC-CSE.
        
        if(CmdFlags.getUseACCSE() || CmdFlags.getUseACCSEAlt()) {
            //  Delete implied sum constraints based on AllDiffs and GCCs. Only when using AC-CSE
            //TransformAlldiffGCCSumDelete tas = new TransformAlldiffGCCSumDelete(m);
            //m.transform(tas);
            tags.removeImpliedConstraints();
        }
        
        ////////////////////////////////////////////////////////////////////////
        //
        //   Decomposition of constraints for SAT
        
        if(CmdFlags.getSattrans() && !propagate) {
            // Decompose some of the global constraints for SAT encoding
            decomposeSatEncoding();
        }
        
        // Plain CSE or Active CSE.
        if (CmdFlags.getUseCSE() || CmdFlags.getUseActiveCSE()) {
            m.transform(tnr);            // Normalise again.
            
            if (CmdFlags.getUseActiveCSE()) {
                CSEActive c = new CSEActive();
                c.flattenCSEs(m);
                m.simplify();
                CmdFlags.stats.put("CSE_active_number", c.numcse);
                CmdFlags.stats.put("CSE_active_eliminated_expressions", c.countcse);
                CmdFlags.stats.put("CSE_active_total_size", c.totallength);
            } else {
                // Identical-CSE.
                CSE c = new CSE();
                c.flattenCSEs(m);
                m.simplify();
                CmdFlags.stats.put("CSE_number", c.numcse);
                CmdFlags.stats.put("CSE_eliminated_expressions", c.countcse);
                CmdFlags.stats.put("CSE_total_size", c.totallength);
            }
        }
        
        if (CmdFlags.getVerbose()) {
            System.out.println("Model may have changed by CSE. Model after rule application:\n" + m.toString());
        }
        
        // Other special cases of flattening. Probably not needed with -deletevars.
        
        TransformEqual t38 = new TransformEqual(m, propagate);
        m.transform(t38);
        
        TransformEqualConst t39 = new TransformEqualConst(propagate);
        m.transform(t39);
        
        if (CmdFlags.table_squash == 1 || CmdFlags.table_squash == 3) {
            TransformShortTableSquash tsts = new TransformShortTableSquash(m);
            m.transform(tsts);
        }
        
        if(CmdFlags.table_squash == 2 || CmdFlags.table_squash == 3) {
            TransformTableToShortTable tttst = new TransformTableToShortTable(m);
            m.transform(tttst);
        }
        ////////////////////////////////////////////////////////////////////////
        //
        // General flattening.
        
        TransformToFlat t4 = new TransformToFlat(m, propagate);
        m.transform(t4);
        
        //  Some further flattening for specific solvers
        if((CmdFlags.getGecodetrans() || CmdFlags.getChuffedtrans()) && !propagate) {
            TransformToFlatGecode tfg=new TransformToFlatGecode(m);
            m.transform(tfg);
        }
        
        // If given the flag to expand short tables, OR output solver does not have short table constraint, then
        // expand short tables to full-length table constraints. 
        if(CmdFlags.getExpandShortTab() || ((CmdFlags.getGecodetrans() || CmdFlags.getChuffedtrans() || CmdFlags.getMinizinctrans()) && !propagate)) {
            TransformExpandShortTable test=new TransformExpandShortTable(m);
            m.transform(test);
        }
        
        ////////////////////////////////////////////////////////////////////////
        //  Remove types that have no output for specific solvers.
        
        if(CmdFlags.getChuffedtrans() && !propagate) {
            TransformModToTable tmtt=new TransformModToTable(m);
            m.transform(tmtt);
        }
        if((CmdFlags.getChuffedtrans() || CmdFlags.getGecodetrans() || CmdFlags.getMinizinctrans()) && !propagate) {
            TransformPowToTable tptt=new TransformPowToTable(m);
            m.transform(tptt);
        }
        
        ////////////////////////////////////////////////////////////////////////
        //  Remove types that have no output to any solver. 
        
        TransformMappingToTable tmtt=new TransformMappingToTable(m);
        m.transform(tmtt);
    }
    
    public ArrayList<ASTNode> postFlattening(int modelnumber, boolean propagate) {
        // Case split for backends
        
        ////////////////////////////////////////////////////////////////////////
        // Branch for Flatzinc output.
        if((CmdFlags.getGecodetrans() || CmdFlags.getChuffedtrans()) && !propagate) {
            fznFlattening();
            System.exit(0);
        }
        
        ////////////////////////////////////////////////////////////////////////
        // Branch for Minizinc output
        if (CmdFlags.getMinizinctrans() && !propagate) {
            minizincOutput();
            System.exit(0);
        }
        
        ////////////////////////////////////////////////////////////////////////
        // Branch for SAT output
        if(CmdFlags.getSattrans() && !propagate) {
            //  Post-flattening decomposition of some constraints. 
            decomposeSatEncodingFlat();
            
            // Final flattening pass removes ToVariable within ToVariable.
            TransformToFlatGecode tfg=new TransformToFlatGecode(m);
            m.transform(tfg);
            
            m.simplify();  // Fix problem with unit vars when outputting sat. 
            
            if(CmdFlags.getTestSolutions()) {
                CmdFlags.checkSolModel=m.copy();
            }
            
            // Discover the variables that need a direct encoding, in addition to the order encoding. 
            TransformCollectSATDirect tcsd=new TransformCollectSATDirect(m);
            tcsd.transform(m.constraints);
            
            CmdFlags.printlnIfVerbose("About to do m.setupSAT");
            
            boolean satenc=m.setupSAT(tcsd.getVarsInConstraints());   //  Create the satModel object and encode the variables.
            
            if(!satenc) {
                // Create .info and .infor files. 
                
                Stats stats=new Stats();
                stats.putValue("SavileRowTotalTime", String.valueOf(((double) System.currentTimeMillis() - CmdFlags.startTime) / 1000));
                stats.putValue("SavileRowClauseOut", "1");
                stats.makeInfoFiles();
                
                CmdFlags.errorExit("Failed when writing SAT encoding to file.");
            }
            
            CmdFlags.printlnIfVerbose("Done m.setupSAT");
            
            //  Do the rewrites that make SATLiterals.
            TransformSATEncoding tse=new TransformSATEncoding(m);
            m.transform(tse);
            
            if(CmdFlags.mining) {
                satOutputMining();
            }
            else {
                satOutput();
            }
            System.exit(0);
        }
        
        ////////////////////////////////////////////////////////////////////////
        //  Minion output. 
        
        //  Get rid of sum equal for Minion.
        TransformSumEq t5 = new TransformSumEq();
        m.transform(t5);
        
        if(CmdFlags.getMakeTables() && !propagate) {
            makeTables();
        }
        
        m.simplify();
        
        // Warm start for optimisation
        if(CmdFlags.getOptWarmStart() && m.objective!=null && propagate) {
            MinionSolver ws = new MinionSolver();
            try {
                Solution sol=ws.optWarmStart(m);
                if(sol!=null) {
                    // Store the solution in case no better one is found, and it
                    // is needed for output. 
                    m.incumbentSolution=sol;
                    
                    // Get the value of the optimisation variable from sol and
                    // add a new constraint 
                    long optval=sol.optval;
                    ASTNode newcon;
                    ASTNode obvar=m.objective.getChild(0);
                    if(m.objective instanceof Minimising) {
                        newcon=new Less(obvar, NumberConstant.make(optval));
                    }
                    else {
                        newcon=new Less(NumberConstant.make(optval), obvar);
                    }
                    System.out.println("Adding warm start constraint: "+newcon); 
                    // Bound the optimisation variable. 
                    m.constraints.getChild(0).setParent(null);  // Do not copy the constraint set.
                    m.constraints.setChild(0, new And(m.constraints.getChild(0), newcon));
                    m.simplify();  // Make the top And flat again. 
                }
            }
            catch(Exception e) {
            }
        }
        
        assert CmdFlags.minionfile != null;
        
        String minfilename = CmdFlags.minionfile;
        if (modelnumber > -1) {
            minfilename = minfilename + "." + modelnumber;
        }
        
        try {
        	FileOutputStream fw=new FileOutputStream(minfilename);
            BufferedWriter out = new BufferedWriter(new OutputStreamWriter(fw));
            m.toMinion(out);
            out.flush();
            fw.getFD().sync();
            out.close();
        } catch (IOException e) {
            CmdFlags.errorExit("Could not open file for Minion output.");
        }
        
        CmdFlags.println("Created output file "+ (propagate?"for domain filtering ":"") + minfilename);
        
        if (propagate) {
            MinionSolver min = new MinionSolver();
            try {
                return min.reduceDomains(CmdFlags.getMinion(), minfilename, m);
            } catch (java.io.IOException e) {
                CmdFlags.errorExit("Could not run Minion: " + e);
            } catch (java.lang.InterruptedException e2) {
                CmdFlags.errorExit("Could not run Minion: " + e2);
            }
        }
        else if (CmdFlags.getRunSolver()) {
            MinionSolver min = new MinionSolver();
            
            try {
                min.findSolutions(CmdFlags.getMinion(), minfilename, m);
            } catch (java.io.IOException e) {
                CmdFlags.errorExit("Could not run Minion: " + e);
            } catch (java.lang.InterruptedException e2) {
                CmdFlags.errorExit("Could not run Minion: " + e2);
            }
        }
        return null;
    }
    
    //  -make-tables flag
    private void makeTables() {
        // Make a table with the scope specified on the command line. 
        
        MinionSolver min = new MinionSolver();
        
        ArrayList<ASTNode> scope=new ArrayList<ASTNode>();
        
        ArrayList<ASTNode> allDecisionVars=new ArrayList<ASTNode>();
        
        categoryentry c=m.global_symbols.category_first;
        while(c!=null) {
            if(c.cat==ASTNode.Decision) {
                //   Deliberately NOT aux vars for now. 
                allDecisionVars.add(new Identifier(m, c.name));
            }
            c=c.next;
        }
        
        for(int i=0; i<CmdFlags.make_tables_scope.size(); i++) {
            scope.add(allDecisionVars.get(CmdFlags.make_tables_scope.get(i)));
        }
        
        ASTNode t=null;
        try {
            t=min.makeTable(m, scope);
        }
        catch( Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
        }
        m.constraints.getChild(0).setParent(null);  //  Do not copy the constraints.
        m.constraints=new Top(new And(m.constraints.getChild(0), t));
        m.simplify();
    }
    
    private void destroyMatrices() {
        boolean has_changed = true;
        while (has_changed) {
            has_changed = false;

            HashMap<String, ASTNode> doms = m.global_symbols.getDomains();
            Iterator<Map.Entry<String, ASTNode>> itr = doms.entrySet().iterator();
            while (itr.hasNext()) {
                Map.Entry<String, ASTNode> a = itr.next();
                if (a.getValue() instanceof MatrixDomain) {
                    if (m.global_symbols.getCategory(a.getKey()) == ASTNode.Decision) {
                        TransformMatrixToAtoms tmta = new TransformMatrixToAtoms(a.getKey(), m);
                        //m.constraints=tmta.transform(m.constraints);
                        m.transform(tmta);
                        has_changed = true;
                        break;
                    }
                }
            }
        }
    }
    
    private void removeMatrixIndexedMatrices() {
        boolean has_changed = true;
        while (has_changed) {
            has_changed = false;

            HashMap<String, ASTNode> doms = m.global_symbols.getDomains();
            Iterator<Map.Entry<String, ASTNode>> itr = doms.entrySet().iterator();
            while (itr.hasNext()) {
                Map.Entry<String, ASTNode> a = itr.next();
                if (a.getValue() instanceof MatrixDomain) {
                    if (m.global_symbols.getCategory(a.getKey()) == ASTNode.Decision) {
                        boolean has_matrix_index=false;
                        for(int i=3; i<a.getValue().numChildren(); i++) {
                            if(a.getValue().getChild(i) instanceof MatrixDomain) has_matrix_index=true;
                        }
                        if(has_matrix_index) {
                            TransformMatrixIndexedMatrix tmim = new TransformMatrixIndexedMatrix(a.getKey(), m);
                            m.transform(tmim);
                            has_changed = true;
                            break;
                        }
                    }
                }
            }
        }
    }
    
    // If the -dominion cmdline option given
    private void classLevelFlattening() {
        System.out.println(m.toString());

        CmdFlags.setAfterAggregate(true);

        // Normalise matrix indices
        // Need to do real normalisation here, because this is before matrix deref
        // is transformed into an arith expression and element constraint
        HashMap<String, ASTNode> doms = m.global_symbols.getDomains();
        Iterator<Map.Entry<String, ASTNode>> itr = doms.entrySet().iterator();
        while (itr.hasNext()) {
            Map.Entry<String, ASTNode> a = itr.next();
            if (a.getValue() instanceof MatrixDomain) {
                TransformMatrixIndicesClass ti = new TransformMatrixIndicesClass(0, m, a.getKey());
                m.transform(ti);
                System.out.println(m.toString());
            }
        }

        ////////////////////////////////////////////////////////////////////////
        //
        // If objective function is not a solitary variable, do one flattening op on it.
        // This is done early because objective has no relational context -- therefore various transformations break on it.

        if (m.objective != null) {
            ASTNode ob = m.objective.getChild(0);
            if (!ob.isConstant() && ! (ob instanceof Identifier)) {
                boolean flatten = true;
                if (ob instanceof MatrixDeref || ob instanceof SafeMatrixDeref) {
                    flatten = false;
                    for (int i =1; i < ob.numChildren(); i++) {
                        if (ob.getChild(i).getCategory() == ASTNode.Decision) {
                            flatten = true;
                        }
                    }
                }

                if (flatten) {
                    PairASTNode bnds = ob.getBoundsAST();
                    ASTNode auxvar = m.global_symbols.newAuxiliaryVariable(bnds.e1, bnds.e2);
                    ASTNode flatcon = new ToVariable(ob, auxvar);
                    m.global_symbols.auxVarRepresentsConstraint(auxvar.toString(), ob.toString());
                    m.objective.setChild(0, auxvar);
                    m.constraints.getChild(0).setParent(null);   //  Do not copy the constraint set.
                    m.constraints.setChild(0, new And(flatcon, m.constraints.getChild(0)));
                }
            }
        }

        ////////////////////////////////////////////////////////////////////////
        // Push And through Forall to produce better Dominion models.
        TransformForallAndToAndForall tfor = new TransformForallAndToAndForall();
        m.transform(tfor);

        ////////////////////////////////////////////////////////////////////////
        // Transform matrix derefs into non-flat element and index aux var.
        TransformMatrixDerefClass tmd = new TransformMatrixDerefClass(m);
        m.transform(tmd);

        ////////////////////////////////////////////////////////////////////////
        // Pre-flattening rearrangement

        TransformOccurrence t35 = new TransformOccurrence();
        m.transform(t35);

        ////////////////////////////////////////////////////////////////////////
        // Sums

        TransformSumEqualSum tses = new TransformSumEqualSum(m);
        m.transform(tses);

        // Same as instance transformation.
        // 1. Transform sum < X  into sum+1 <= X

        TransformSumLess t36 = new TransformSumLess();
        m.transform(t36);

        // 2. Transform sum1 <= sum2 into (sum1 - sum2) <= 0
        // so that it goes into one sumleq constraint.

        TransformSumLeq t37 = new TransformSumLeq();
        m.transform(t37);

        ////////////////////////////////////////////////////////////////////////
        // Mappers
        
        if (CmdFlags.getUseMappers()) {
            TransformSumToShift tsts = new TransformSumToShift(m);
            m.transform(tsts);

            TransformProductToMult tptm = new TransformProductToMult(m);
            m.transform(tptm);
        }
        if (CmdFlags.getUseMinionMappers()) {
            // Just deal with quantified sum -- weighted sum is already OK.
            TransformProductToMultInQSum tptm = new TransformProductToMultInQSum(m);
            m.transform(tptm);
        }
        if (!CmdFlags.getUseMappers() && !CmdFlags.getUseMinionMappers()) {
            // Turn weighted sum into plain sum
            TransformWSumToSum twsts = new TransformWSumToSum(m);
            m.transform(twsts);
        }
        
        ////////////////////////////////////////////////////////////////////////
        //
        // Special cases of flattening

        // CSE goes here in instance-level sequence
        if (CmdFlags.getUseCSE()) {
            CSEClassIdentical c = new CSEClassIdentical();            // This doesn't work.
            c.flattenCSEs(m);
            m.simplify();
        }

        ////////////////////////////////////////////////////////////////////////
        //
        // Before general flattening, deal with N-ary Times which can't appear in the output.
        CmdFlags.setOutputReady(true);

        TransformTimes ttimes = new TransformTimes(m);
        m.transform(ttimes);

        // More special cases of flattening.

        TransformEqualClass t38 = new TransformEqualClass(m);
        m.transform(t38);

        TransformEqualConstClass tec = new TransformEqualConstClass();
        m.transform(tec);

        ////////////////////////////////////////////////////////////////////////
        //
        // General flattening.

        TransformToFlatClass tf = new TransformToFlatClass(m);
        m.transform(tf);

        ////////////////////////////////////////////////////////////////////////
        // Tidy up

        TransformConstMatrixClass tcmc = new TransformConstMatrixClass(m);
        m.transform(tcmc);

        System.out.println("**** Completed class-level flattening ****");
        System.out.println(m.toString());

        // Now shift matrices to 0-based again, to deal with the new ones.
        // Can do this because all matrix derefs have only parameter expressions
        // as indices.
        doms = m.global_symbols.getDomains();
        itr = doms.entrySet().iterator();
        while (itr.hasNext()) {
            Map.Entry<String, ASTNode> a = itr.next();
            if (a.getValue() instanceof MatrixDomain) {
                boolean needsShift = false;
                ArrayList<ASTNode> indices = ((MatrixDomain) a.getValue()).getMDIndexDomains();
                for (int i =0; i < indices.size(); i++) {
                    if (! indices.get(i).getBoundsAST().e1.equals(NumberConstant.make(0))) {
                        needsShift = true;
                        break;
                    }
                }

                if (needsShift) {
                    CmdFlags.println("About to normalise indices of matrix: " + a.getKey());

                    TransformMatrixIndicesClass ti = new TransformMatrixIndicesClass(0, m, a.getKey());
                    m.transform(ti);
                    System.out.println(m.toString());
                }
            }
        }

        m.simplify();

        System.out.println("************************");
        System.out.println("**** After Simplify ****");
        System.out.println("************************");
        System.out.println(m.toString());

        System.out.println("************************");
        System.out.println("**** Dominion output ***");
        System.out.println("************************");
        StringBuilder b = new StringBuilder();
        m.toDominion(b);
        System.out.println(b.toString());

        try {
            BufferedWriter out;
            out = new BufferedWriter(new FileWriter(CmdFlags.dominionfile));
            out.append(b);
            out.close();
        } catch (IOException e) {
            CmdFlags.errorExit("Could not open file for Dominion output.");
        }

        // TODO
        // 2. fix aux6[i]=aux7 malarky.
    }

    // If the -gecode or -chuffed cmdline option given
    private void fznFlattening() {
        // Flattening is done already.
        TransformSumEqToSum t1 = new TransformSumEqToSum();
        m.transform(t1);
        
        // Get rid of some reified constraints where Gecode does not implement them.
        TransformReifyMin trm = new TransformReifyMin(m);
        m.transform(trm);
        
        TransformAbsReify tar = new TransformAbsReify(m);
        m.transform(tar);
        
        m.simplify();
        
        // THE VERY LAST THING must be to collect bool and int vars.
        TransformCollectBool tcb = new TransformCollectBool(m);
        m.transform(tcb);
        
        try {
            BufferedWriter out;
            out = new BufferedWriter(new FileWriter(CmdFlags.fznfile));
            m.toFlatzinc(out);
            out.close();
        } catch (IOException e) {
            CmdFlags.errorExit("Could not open file for flatzinc output.");
        }
        
        CmdFlags.println("Created output file " + CmdFlags.fznfile);
        
        if (CmdFlags.getRunSolver()) {
            FznSolver fz = new FznSolver();
            
            try {
                String solbin=(CmdFlags.getGecodetrans())?CmdFlags.getGecode():CmdFlags.getChuffed();
                fz.findSolutions(solbin, CmdFlags.fznfile, m);
            } catch (java.io.IOException e) {
                CmdFlags.errorExit("Could not run flatzinc solver: " + e);
            } catch (java.lang.InterruptedException e2) {
                CmdFlags.errorExit("Could not run flatzinc solver: " + e2);
            }
        }

    }
    
    // If the -minizinc cmdline option given
    private void minizincOutput() {
        // Flattening is done already.
        
        // THE VERY LAST THING must be to collect bool and int vars.
        TransformCollectBool tcb = new TransformCollectBool(m);
        m.transform(tcb);
        
        StringBuilder b = new StringBuilder();
        m.toMinizinc(b);

        try {
            BufferedWriter out;
            out = new BufferedWriter(new FileWriter(CmdFlags.minizincfile));
            out.append(b);
            out.close();
        } catch (IOException e) {
            CmdFlags.errorExit("Could not open file for minizinc output.");
        }
        
        CmdFlags.println("Created output file " + CmdFlags.minizincfile);
    }
    
    // Decompose some constraints for SAT output. Occurs before flattening.
    private void decomposeSatEncoding() {
        
        //  Two options for alldiff -- atmost constraints or pairwise binary decomposition.
        if(true) {
            TransformAlldiffToAtmost taa= new TransformAlldiffToAtmost(m);
            m.transform(taa);
        }
        else {
            TransformDecomposeAlldiff tda= new TransformDecomposeAlldiff(m);
            m.transform(tda);
        }
        
        TransformGCCToSums tgts=new TransformGCCToSums();
        m.transform(tgts);
        
        TransformCountToSum tcts=new TransformCountToSum();
        m.transform(tcts);
        
        TransformOccurrenceToSum tots=new TransformOccurrenceToSum();
        m.transform(tots);
        
        if(CmdFlags.getSatDecompCSE()) {
            TransformDecomposeLex2 tdlx=new TransformDecomposeLex2(m);
            m.transform(tdlx);
        }
        else {
            TransformDecomposeLex tdlx=new TransformDecomposeLex(m);
            m.transform(tdlx);
        }
    }
    
    //  Further decompositions that are applied after flattening/CSE.
    private void decomposeSatEncodingFlat() {
        
        // Decompose constraints made from functions by ToVariable. 
        TransformDecomposeMinMax tdmm=new TransformDecomposeMinMax(m);
        m.transform(tdmm);
        
        // This may unflatten when we have a reified element ct.
        TransformElementForSAT2 tefs=new TransformElementForSAT2(m);
        m.transform(tefs);
        
        //  Break up sums for SAT output. 
        //  Special cases first, where a non-default encoding has been specified on the command-line.
        if(CmdFlags.getSatAlt()) {
            //  This branch treats sums like product etc. End up with flat x+y=z type constraints
            //  that are then encoded using the toSATWithAuxVar method in WeightedSum -- same as product etc. 
            // Sort sums by coefficient size.
            TransformSortWeightedSum2 tsort=new TransformSortWeightedSum2();
            m.transform(tsort);
            
            TransformBreakupSum tbs=new TransformBreakupSum(m);
            m.constraints=tbs.transform(m.constraints);
        }
        else {
            //  Default case. 
            // Rearrange sums to have all non-constant terms on one side of binop.
            TransformSumForSAT t1=new TransformSumForSAT();
            m.transform(t1);
            
            if(CmdFlags.getSatMDD()) {
                //  Catch AMO-PB constraints so they can be encoded using the MDD encoding
                TransformSumToAMOPB tpb=new TransformSumToAMOPB();
                m.transform(tpb);
            }
            
            if(false) {
                // Sort sums by coefficient size.
                TransformSortWeightedSum2 tsort=new TransformSortWeightedSum2();
                m.transform(tsort);
                
                TransformBreakupSum tbs=new TransformBreakupSum(m);
                m.constraints=tbs.transform(m.constraints);
                
                TransformToFlat ttf=new TransformToFlat(m, false); // Assumes SAT output is not used for preprocessing. 
                m.transform(ttf);
            }
            else {
                // Special cases of sum on bools.
                // sum=1, sum=0, sum<=0, sum<=1, sum<1, sum<2
                
                TransformEncodeSumSpecial tess=new TransformEncodeSumSpecial(m);
                //m.transform(tess);
                
                m.simplify();   // This should not be necessary: avoid problem with knapsack where deleted variable breaks the following pass.
                
                //   Tree decomp of sum.
                TransformBreakupSum2 tbs=new TransformBreakupSum2(m);
                m.transform(tbs);
            }
            
            // Get rid of sum equal, leaving only inequalities
            TransformSumEq t5 = new TransformSumEq();
            m.transform(t5);
            
            // Rearrange sums to have all non-constant terms on one side of binop.  -- Second pass required following breakup pass.
            m.transform(t1);
            
            
            // Sort sums by coefficient -- prob. to reduce number of iterations in order encoding of ct.
            TransformWeightedSumForSAT t6=new TransformWeightedSumForSAT();
            m.transform(t6);
            
            
        }
        
        //  TransformElementForSAT2 produces non-flat output when there is a reified element constraint. 
        TransformToFlat ttf=new TransformToFlat(m, false); // Assumes SAT output is not used for preprocessing. 
        m.transform(ttf);
    }
    
    // If the -sat cmdline option given
    private void satOutput() {
        boolean satenc=m.toSAT();
        
        if(!satenc) {
            // Create .info and .infor files. 
            Stats stats=new Stats();
            stats.putValue("SavileRowTotalTime", String.valueOf(((double) System.currentTimeMillis() - CmdFlags.startTime) / 1000));
            stats.putValue("SavileRowClauseOut", "1");
            stats.makeInfoFiles();
            
            CmdFlags.errorExit("Failed when writing SAT encoding to file.");
        }
        
        CmdFlags.println("Created output SAT file " + CmdFlags.satfile);
        
        if(CmdFlags.getRunSolver()) {
            SATSolver solver;
            
            if(CmdFlags.getMaxsattrans()) {
                solver=new OpenWBOSATSolver(m);
            }
            else {
                if(CmdFlags.getSatFamily().equals("minisat")) {
                    solver=new MinisatSATSolver(m);
                }
                else if(CmdFlags.getSatFamily().equals("glucose")) {
                    solver=new GlucoseSATSolver(m);
                }
                else if( (CmdFlags.getSatFamily().equals("nbc_minisat_all")) || (CmdFlags.getSatFamily().equals("bc_minisat_all"))) {
                    solver=new AllMinisatSATSolver(m);
                }
                else {
                    assert CmdFlags.getSatFamily().equals("lingeling");
                    solver=new LingelingSATSolver(m);
                }
            }
            
            try {
                solver.findSolutions(CmdFlags.getSatSolver(), CmdFlags.satfile, m);
            } catch (Exception e) {
                CmdFlags.errorExit("Could not run SAT solver: " + e);
            }
            
            //  Delete the dimacs file because it may be very large. 
            File f = new File(CmdFlags.satfile);
            if (f.exists()) f.delete();
        }
    }
    
    // If the -sat cmdline option given
    private void satOutputMining() {
        //  Pull out the cardinality constraint from the constraint set.
        ASTNode card=null;
        ASTNode cardlist=null;
        ASTNode incl=MultiStageOnSolution.incl;
        ASTNode topand=m.constraints.getChild(0);
        
        if(topand instanceof And) {
            for(int i=0; i<topand.numChildren() && (card==null || incl==null); i++) {
                if(topand.getChild(i) instanceof MultiStage) {
                    card=topand.getChild(i).getChild(0);
                    cardlist=topand.getChild(i).getChild(1);
                    topand.setChild(i, new BooleanConstant(true));
                }
                /*if(topand.getChild(i) instanceof MultiStageOnSolution) {
                    incl=topand.getChild(i).getChild(0);
                    topand.setChild(i, new BooleanConstant(true));
                }*/
            }
        }
        else if(topand instanceof MultiStage) {
            //  All other constraints have been removed
            card=topand.getChild(0);
            cardlist=topand.getChild(1);
            m.constraints.setChild(0, new BooleanConstant(true));
        }
        
        if(card==null) {
            CmdFlags.errorExit("Could not find multiStage function.");
        }
        if(incl==null) {
            CmdFlags.errorExit("Could not find multiStageOnSolution function.");
        }
        
        // remove the trues. 
        m.simplify();
        
        boolean satenc=m.toSAT();
        
        if(!satenc) {
            // Create .info and .infor files. 
            Stats stats=new Stats();
            stats.putValue("SavileRowTotalTime", String.valueOf(((double) System.currentTimeMillis() - CmdFlags.startTime) / 1000));
            stats.putValue("SavileRowClauseOut", "1");
            stats.makeInfoFiles();
            
            CmdFlags.errorExit("Failed when writing SAT encoding to file.");
        }
        
        CmdFlags.println("Created output SAT file " + CmdFlags.satfile);
        
        try {
            // Store the current state of the sat file -- current file size, variables, clauses.
            m.satModel.BTMark();
            
            // Get value set of the cardinality expression
            ArrayList<Intpair> cardvalsset=card.getIntervalSetExp();
            
            BufferedWriter out = new BufferedWriter(new FileWriter(CmdFlags.infofile, false));
            out.close();
            
            // Construct solver object.
            SATSolver solver;
            
            if(CmdFlags.getMaxsattrans()) {
                solver=new OpenWBOSATSolver(m);
            }
            else {
                if(CmdFlags.getSatFamily().equals("minisat")) {
                    solver=new MinisatSATSolver(m);
                }
                else if(CmdFlags.getSatFamily().equals("glucose")) {
                    solver=new GlucoseSATSolver(m);
                }
                else if( (CmdFlags.getSatFamily().equals("nbc_minisat_all")) || (CmdFlags.getSatFamily().equals("bc_minisat_all"))) {
                    solver=new AllMinisatSATSolver(m);
                }
                else {
                    assert CmdFlags.getSatFamily().equals("lingeling");
                    solver=new LingelingSATSolver(m);
                }
            }
            
            cardvalueloop:
            for(int cardvalueidx=1; cardvalueidx<cardlist.numChildren(); cardvalueidx++) {
                long cardvalue=cardlist.getChild(cardvalueidx).getValue();
                if(! Intpair.contains(cardvalsset, cardvalue)) {
                    continue cardvalueloop;
                }
                
                System.out.println("Looking for itemsets of size: "+cardvalue);
                
                //  Put the number into the info file. 
                out= new BufferedWriter(new FileWriter(CmdFlags.infofile, true));
                out.write("Cardinality:"+String.valueOf(cardvalue)+"\n");
                out.close();
                
                //  Make the new constraint for the cardinality
                ASTNode c1=new And(new LessEqual(card, NumberConstant.make(cardvalue)),
                    new LessEqual(NumberConstant.make(cardvalue), card));
                
                //  Re-open the sat file.
                m.satModel.reopenFile();
                
                //  Make the new constraints to exclude subsets of previously found itemsets with the same frequency.
                TransformSATEncoding tse=new TransformSATEncoding(m);
                
                if(MultiStageOnSolution.sollist!=null) {
                    TransformQuantifiedExpression tqe=new TransformQuantifiedExpression(m);
                    TransformSimplify ts=new TransformSimplify();
                    
                    HashMap<String, ASTNode> sol_hash=new HashMap<String, ASTNode>();
                    for(int i=0; i<MultiStageOnSolution.sollist.size(); i++) {
                        ASTNode sol=MultiStageOnSolution.sollist.get(i);
                        
                        ASTNode ctcopy=incl.copy();
                        
                        for(int j=0; j<sol.numChildren(); j++) {
                            sol_hash.put(sol.getChild(j).getChild(0).toString(), sol.getChild(j).getChild(1));
                        }
                        
                        //  Sub in value of X from the solution, replacing fromSolution(X) function.
                        TransformSubInSolution tsis=new TransformSubInSolution(sol_hash);
                        ctcopy=tsis.transform(ctcopy);
                        
                        ctcopy=ts.transform(tqe.transform(ts.transform(ctcopy)));
                        
                        ctcopy=tse.transform(ctcopy);
                        
                        //  Encode the constraint.
                        ctcopy.toSAT(m.satModel);
                    }
                }
                
                //   Commit to the above encoding of exclusion constraints.
                m.satModel.finaliseOutput();
                m.satModel.BTMark();
                //  Clear solutions to avoid encoding them multiple times. 
                if(MultiStageOnSolution.sollist!=null) {
                    MultiStageOnSolution.sollist.clear();
                }
                
                m.satModel.reopenFile();
                
                c1=tse.transform(c1);
                c1.toSAT(m.satModel);  // Cardinality
                
                m.satModel.finaliseOutput();
                
                try {
                    solver.findSolutions(CmdFlags.getSatSolver(), CmdFlags.satfile, m);
                } catch (Exception e) {
                    CmdFlags.errorExit("Could not run SAT solver: " + e);
                }
                
                //  Restore the state of the DIMACS file and the Sat object before the next iteration.
                m.satModel.BTRestore();
            }
        }
        catch(IOException ioe) {
            CmdFlags.errorExit("By 'eck.");
        }
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    // Deal with statements in the preamble.
    
    private void processGiven(ASTNode giv) {
        ASTNode id = giv.getChild(0);
        String idname = ((Identifier) id).getName();
        ASTNode dom = giv.getChild(1);
        
        // Insert into symbol table as a parameter, with the given domain.
        if (m.global_symbols.hasVariable(idname)) {
            CmdFlags.errorExit("Symbol " + idname + " declared twice.");
        }
        m.global_symbols.newVariable(idname, dom, ASTNode.Parameter);
        
        if (!CmdFlags.getDominiontrans()) {            // If doing instance transformation, look in the parameter file.
            int num_lettings =0;
            ASTNode param = null;
            for (ASTNode p : parameters) {
                if (((Identifier) ((Letting) p).getChildren().get(0)).getName().equals(idname)) {
                    param = p;
                    num_lettings++;
                }
            }
            if (num_lettings != 1) {
                CmdFlags.errorExit("Parameter ('given') variable " + idname + " is defined "+num_lettings+" times in parameter file.");
            }
            
            processLetting(param);
            parameters.remove(param);
        }
    }
    
    private void processLetting(ASTNode let) {
        assert let instanceof Letting;
        
        ASTNode id = let.getChild(0);
        String idname = ((Identifier) id).getName();
        if (m.global_symbols.hasVariable(idname) && m.global_symbols.getCategory(idname) != ASTNode.Parameter) {
            CmdFlags.errorExit("Symbol " + idname + " declared more than once.");
        }
        ASTNode value = let.getChild(1);
        
        if (value.getCategory() > ASTNode.Quantifier) {
            CmdFlags.errorExit("In statement: " + let, "Right-hand side contains an identifier that is not a constant or parameter.");
        }
        
        if (value instanceof CompoundMatrix || value instanceof EmptyMatrix) {
            // Put into symbol table
            // No need for domain in letting because the matrix literal has been adjusted to be consistent with the domain in the letting.
            m.cmstore.newConstantMatrix(idname, value);
            
            // Adding a constant matrix may make some lettings appear, inferred from the dimensions.
            
            ArrayList<ASTNode> newlets = m.cmstore.makeLettingsConstantMatrix(idname);
            for (ASTNode l2 : newlets) {
                processLetting(l2);
            }
            
            // Now fit the matrix literal to the domain in the symbol table if this is possible.
            // The domain in the symbol table either came from a letting or a given.
            // If it came from the letting, we are repeating work here (unfortunate but not wrong).
            // If it came from the given, we need to do this.
            m.cmstore.correctIndicesConstantMatrix(idname, true);
        }
        else {            // Substitute it everywhere.
            // m.global_symbols.newVariable(idname, ASTNode.Constant);  // NEED to do something here -- take the given out of the s-table and replace it with a constant.
            m.substitute(let.getChild(0), value.copy());
        }
    }
    
    private void processFind(ASTNode find) {
        assert find instanceof Find;
        ASTNode id = find.getChild(0);
        String idname = ((Identifier) id).getName();
        if (m.global_symbols.hasVariable(idname)) {
            CmdFlags.errorExit("Symbol " + idname + " declared more than once.");
        }
        
        if (find.getChild(1).getCategory() > ASTNode.Quantifier) {
            CmdFlags.errorExit("In statement : " + find, "Right-hand side contains an identifier that is not a constant or parameter.");
        }
        m.global_symbols.newVariable(idname, find.getChild(1), ASTNode.Decision);
    }

    private void processWhere(ASTNode a) {
        if (CmdFlags.getDominiontrans()) {
            // Should store the where and output it. But there is no where statement in DIL.
            return;
        } else {
            a = a.getChild(0);            // get the actual statement
            // Quantifier expressions should already have been unrolled by now.
            if (a.getCategory() > ASTNode.Quantifier) {
                CmdFlags.errorExit("In statement: where " + a, "Contains an identifier that is not a constant or parameter.");
            }
            if (! a.equals(new BooleanConstant(true))) {
                CmdFlags.errorExit("In statement: where " + a, "Does not evaluate to true.");
            }
        }
    }
    
    // Takes a letting and repairs the index domains in the constant
    // matrix using the matrix domain in the letting (if there is one).
    // Always returns a letting without a domain.
    private ASTNode fixIndexDomainsLetting(ASTNode a) {
        if (a.numChildren() == 3) {
            ASTNode mat = a.getChild(1);
            if (mat instanceof CompoundMatrix || mat instanceof EmptyMatrix) {
                Pair<ASTNode, Boolean> p = ConstantMatrixStore.fixIndicesConstantMatrix(a.getChild(2), mat.copy());
                if (p.getSecond()) {
                    CmdFlags.warning("The index domains in the matrix literal do not match");
                    CmdFlags.warning("the given matrix domain in the following letting statement:");
                    CmdFlags.warning(String.valueOf(a));
                }
                
                return new Letting(a.getChild(0), p.getFirst());
            }
        }
        return a;
    }
    
    public ModelContainer copy() {
        Model mcopy=m.copy();
        ArrayList<ASTNode> paramcopy=new ArrayList<ASTNode>();
        TransformFixSTRef tf=new TransformFixSTRef(mcopy);
        for(int i=0; i<parameters.size(); i++) {
            paramcopy.add(tf.transform(parameters.get(i)));
        }
        return new ModelContainer(mcopy, paramcopy);
    }
    
    public void writeModelAsJSON(Model m) {
        SymmetryBreaker  s = new SymmetryBreaker ();
        s.detectAndBreakSymmetries(m);
        m.simplify();
    }
}
