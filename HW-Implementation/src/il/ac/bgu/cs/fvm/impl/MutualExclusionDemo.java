package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;

import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.examples.PetersonProgramGraphBuilder;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedActDef;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedCondDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import il.ac.bgu.cs.fvm.verification.VerificationSucceeded;
import il.ac.bgu.cs.fvm.impl.AutomataFactory;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.seq;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;

public class MutualExclusionDemo {
	private static FvmFacade fvmFacadeImpl;
	 	
	    public static void main(String[] args){
	    System.out.println("Start mutual exclusion demo");	
	    System.out.println("Init fvm instance");	
    	fvmFacadeImpl = FvmFacade.createInstance();
    	System.out.println("Create pg1");	
		ProgramGraph<String, String> pg1 = PetersonProgramGraphBuilder.build(1);
		System.out.println("Create pg2");	
		ProgramGraph<String, String> pg2 = PetersonProgramGraphBuilder.build(2);
		System.out.println("Create and Interleave two Peterson program graphs-pg1 and pg2");
		ProgramGraph<Pair<String, String>, String> pg = fvmFacadeImpl.interleave(pg1, pg2);
		Set<ActionDef> ad = set(new ParserBasedActDef());
		Set<ConditionDef> cd = set(new ParserBasedCondDef());
		System.out.println("Create transition system from program graph-the interleaved program graph");
		TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts;
		ts = fvmFacadeImpl.transitionSystemFromProgramGraph(pg, ad, cd);
		// Add labels to ts for formulating mutual exclusion properties.
		ts.getStates().stream().forEach(st -> ts.getAtomicPropositions().stream().forEach(ap -> ts.removeLabel(st, ap)));

		Set<String> aps = new HashSet<>(ts.getAtomicPropositions());
		aps.stream().forEach(ap -> ts.removeAtomicProposition(ap));

		seq("wait1", "wait2", "crit1", "crit2", "crit1_enabled").stream().forEach(s -> ts.addAtomicPropositions(s));

		ts.getStates().stream().filter(s -> s.getFirst().getFirst().equals("crit1")).forEach(s -> ts.addToLabel(s, "crit1"));
		ts.getStates().stream().filter(s -> s.getFirst().getFirst().equals("wait1")).forEach(s -> ts.addToLabel(s, "wait1"));

		ts.getStates().stream().filter(s -> s.getFirst().getSecond().equals("crit2")).forEach(s -> ts.addToLabel(s, "crit2"));
		ts.getStates().stream().filter(s -> s.getFirst().getSecond().equals("wait2")).forEach(s -> ts.addToLabel(s, "wait2"));

		Predicate<Pair<Pair<String, String>, ?>> _crit1 = ss -> ss.getFirst().getFirst().equals("crit1");
		ts.getStates().stream().filter(s -> fvmFacadeImpl.post(ts, s).stream().anyMatch(_crit1)).forEach(s -> ts.addToLabel(s, "crit1_enabled"));
		// End add labels
		// Test mutual exclusion
		System.out.println("Create automaton for mutex");
		Automaton<String, String> aut = new AutomataFactory<>(ts).eventuallyPhiAut(a -> a.contains("crit1") && a.contains("crit2"));
		System.out.println("Verify omega regular property-mutex");
		VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> vr = fvmFacadeImpl.verifyAnOmegaRegularProperty(ts, aut);
		if(vr instanceof VerificationSucceeded) {
	        System.out.println("Mutex verification succeeded");

		}
		else {
	        System.out.println("Mutex verification failed");

		}
    	// Test a liveness property - that after every state that satisfies
 		// wait1 we must eventually have a state that satisfies crit1
        System.out.println("Create automaton for starvation");
		Automaton<String, String> aut2 = new AutomataFactory<>(ts).eventuallyPhi1AndThenAlwaysPhi2Aut(a -> a.contains("wait1"), a -> !a.contains("crit1"));
	    System.out.println("Verify omega regular property-starvation");
		VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> vr2 = fvmFacadeImpl.verifyAnOmegaRegularProperty(ts, aut2);
		if(vr2 instanceof VerificationSucceeded) {
	        System.out.println("Starvation verification succeeded");

		}
		else {
	        System.out.println("Starvation verification failed");

		}
	}   
		
}

