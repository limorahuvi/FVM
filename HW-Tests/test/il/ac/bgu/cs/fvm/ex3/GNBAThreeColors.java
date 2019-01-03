package il.ac.bgu.cs.fvm.ex3;

import static il.ac.bgu.cs.fvm.util.CollectionHelper.p;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;
import static org.junit.Assert.assertEquals;

import java.util.Set;

import org.junit.Test;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.util.Util;

public class GNBAThreeColors {
	FvmFacade fvmFacadeImpl = FvmFacade.createInstance();

	@Test
	public void threeColorTest() throws Exception {

		MultiColorAutomaton<String, String> mulAut = getMCAut();

		Automaton<?, String> aut = fvmFacadeImpl.GNBA2NBA(mulAut);

		assertEquals(aut, getExpected());

	}

	MultiColorAutomaton<String, String> getMCAut() {
		MultiColorAutomaton<String, String> aut = new MultiColorAutomaton<>();

		for (Set<String> s : Util.powerSet(set("a", "b", "c"))) {
			aut.addTransition("s0", s, "s4");
			aut.addTransition("s1", s, "s4");
			aut.addTransition("s2", s, "s4");
			aut.addTransition("s3", s, "s4");
			aut.addTransition("s4", s, "s4");
			aut.addTransition("s5", s, "s4");
			aut.addTransition("s6", s, "s4");
			aut.addTransition("s7", s, "s4");
		}

		aut.addTransition("s0", set("a"), "s2");
		aut.addTransition("s0", set("b"), "s0");
		aut.addTransition("s0", set("c"), "s1");
		aut.addTransition("s0", set("a", "b"), "s5");
		aut.addTransition("s0", set("a", "c"), "s6");
		aut.addTransition("s0", set("a", "b", "c"), "s7");
		aut.addTransition("s0", set("b", "c"), "s3");
		aut.addTransition("s1", set("a"), "s2");
		aut.addTransition("s1", set("b"), "s0");
		aut.addTransition("s1", set("c"), "s1");
		aut.addTransition("s1", set("a", "b"), "s5");
		aut.addTransition("s1", set("a", "c"), "s6");
		aut.addTransition("s1", set("b", "c"), "s3");
		aut.addTransition("s1", set("a", "b", "c"), "s7");
		aut.addTransition("s2", set("a"), "s2");
		aut.addTransition("s2", set("b"), "s0");
		aut.addTransition("s2", set("c"), "s1");
		aut.addTransition("s2", set("a", "b"), "s5");
		aut.addTransition("s2", set("a", "c"), "s6");
		aut.addTransition("s2", set("b", "c"), "s3");
		aut.addTransition("s2", set("a", "b", "c"), "s7");
		aut.addTransition("s3", set("a"), "s2");
		aut.addTransition("s3", set("b"), "s0");
		aut.addTransition("s3", set("c"), "s1");
		aut.addTransition("s3", set("a", "b"), "s5");
		aut.addTransition("s3", set("a", "c"), "s6");
		aut.addTransition("s3", set("b", "c"), "s3");
		aut.addTransition("s3", set("a", "b", "c"), "s7");
		aut.addTransition("s4", set("a"), "s2");
		aut.addTransition("s4", set("b"), "s0");
		aut.addTransition("s4", set("c"), "s1");
		aut.addTransition("s4", set("a", "b"), "s5");
		aut.addTransition("s4", set("a", "c"), "s6");
		aut.addTransition("s4", set("b", "c"), "s3");
		aut.addTransition("s4", set("a", "b", "c"), "s7");
		aut.addTransition("s5", set("a"), "s2");
		aut.addTransition("s5", set("b"), "s0");
		aut.addTransition("s5", set("c"), "s1");
		aut.addTransition("s5", set("a", "b"), "s5");
		aut.addTransition("s5", set("a", "c"), "s6");
		aut.addTransition("s5", set("b", "c"), "s3");
		aut.addTransition("s5", set("a", "b", "c"), "s7");
		aut.addTransition("s6", set("a"), "s2");
		aut.addTransition("s6", set("b"), "s0");
		aut.addTransition("s6", set("c"), "s1");
		aut.addTransition("s6", set("a", "b"), "s5");
		aut.addTransition("s6", set("a", "c"), "s6");
		aut.addTransition("s6", set("b", "c"), "s3");
		aut.addTransition("s6", set("a", "b", "c"), "s7");
		aut.addTransition("s7", set("a"), "s2");
		aut.addTransition("s7", set("b"), "s0");
		aut.addTransition("s7", set("c"), "s1");
		aut.addTransition("s7", set("a", "b"), "s5");
		aut.addTransition("s7", set("a", "c"), "s6");
		aut.addTransition("s7", set("b", "c"), "s3");
		aut.addTransition("s7", set("a", "b", "c"), "s7");

		aut.setInitial("s0");

		aut.setAccepting("s0", 11);
		aut.setAccepting("s3", 11);
		aut.setAccepting("s5", 11);
		aut.setAccepting("s7", 11);

		aut.setAccepting("s1", 22);
		aut.setAccepting("s3", 22);
		aut.setAccepting("s6", 22);
		aut.setAccepting("s7", 22);

		aut.setAccepting("s2", 33);
		aut.setAccepting("s5", 33);
		aut.setAccepting("s6", 33);
		aut.setAccepting("s7", 33);

		return aut;

	}

	@SuppressWarnings("unchecked")
	Automaton<Pair<Integer, Integer>, String> getExpected() {
		Automaton<Pair<Integer, Integer>, String> aut = new Automaton<>();

		aut.addTransition(p(0, 1), set(), p(4, 2));
		aut.addTransition(p(0, 1), set("a"), p(2, 2));
		aut.addTransition(p(0, 1), set("a"), p(4, 2));
		aut.addTransition(p(0, 1), set("b"), p(0, 2));
		aut.addTransition(p(0, 1), set("b"), p(4, 2));
		aut.addTransition(p(0, 1), set("c"), p(1, 2));
		aut.addTransition(p(0, 1), set("c"), p(4, 2));
		aut.addTransition(p(0, 1), set("a", "b"), p(4, 2));
		aut.addTransition(p(0, 1), set("a", "b"), p(5, 2));
		aut.addTransition(p(0, 1), set("a", "c"), p(4, 2));
		aut.addTransition(p(0, 1), set("a", "c"), p(6, 2));
		aut.addTransition(p(0, 1), set("b", "c"), p(3, 2));
		aut.addTransition(p(0, 1), set("b", "c"), p(4, 2));
		aut.addTransition(p(0, 1), set("a", "b", "c"), p(4, 2));
		aut.addTransition(p(0, 1), set("a", "b", "c"), p(7, 2));
		aut.addTransition(p(0, 2), set(), p(4, 2));
		aut.addTransition(p(0, 2), set("a"), p(2, 2));
		aut.addTransition(p(0, 2), set("a"), p(4, 2));
		aut.addTransition(p(0, 2), set("b"), p(0, 2));
		aut.addTransition(p(0, 2), set("b"), p(4, 2));
		aut.addTransition(p(0, 2), set("c"), p(1, 2));
		aut.addTransition(p(0, 2), set("c"), p(4, 2));
		aut.addTransition(p(0, 2), set("a", "b"), p(4, 2));
		aut.addTransition(p(0, 2), set("a", "b"), p(5, 2));
		aut.addTransition(p(0, 2), set("a", "c"), p(4, 2));
		aut.addTransition(p(0, 2), set("a", "c"), p(6, 2));
		aut.addTransition(p(0, 2), set("b", "c"), p(3, 2));
		aut.addTransition(p(0, 2), set("b", "c"), p(4, 2));
		aut.addTransition(p(0, 2), set("a", "b", "c"), p(4, 2));
		aut.addTransition(p(0, 2), set("a", "b", "c"), p(7, 2));
		aut.addTransition(p(1, 1), set(), p(4, 1));
		aut.addTransition(p(1, 1), set("a"), p(2, 1));
		aut.addTransition(p(1, 1), set("a"), p(4, 1));
		aut.addTransition(p(1, 1), set("b"), p(0, 1));
		aut.addTransition(p(1, 1), set("b"), p(4, 1));
		aut.addTransition(p(1, 1), set("c"), p(1, 1));
		aut.addTransition(p(1, 1), set("c"), p(4, 1));
		aut.addTransition(p(1, 1), set("a", "b"), p(4, 1));
		aut.addTransition(p(1, 1), set("a", "b"), p(5, 1));
		aut.addTransition(p(1, 1), set("a", "c"), p(4, 1));
		aut.addTransition(p(1, 1), set("a", "c"), p(6, 1));
		aut.addTransition(p(1, 1), set("b", "c"), p(3, 1));
		aut.addTransition(p(1, 1), set("b", "c"), p(4, 1));
		aut.addTransition(p(1, 1), set("a", "b", "c"), p(4, 1));
		aut.addTransition(p(1, 1), set("a", "b", "c"), p(7, 1));
		aut.addTransition(p(1, 2), set(), p(4, 3));
		aut.addTransition(p(1, 2), set("a"), p(2, 3));
		aut.addTransition(p(1, 2), set("a"), p(4, 3));
		aut.addTransition(p(1, 2), set("b"), p(0, 3));
		aut.addTransition(p(1, 2), set("b"), p(4, 3));
		aut.addTransition(p(1, 2), set("c"), p(1, 3));
		aut.addTransition(p(1, 2), set("c"), p(4, 3));
		aut.addTransition(p(1, 2), set("a", "b"), p(4, 3));
		aut.addTransition(p(1, 2), set("a", "b"), p(5, 3));
		aut.addTransition(p(1, 2), set("a", "c"), p(4, 3));
		aut.addTransition(p(1, 2), set("a", "c"), p(6, 3));
		aut.addTransition(p(1, 2), set("b", "c"), p(3, 3));
		aut.addTransition(p(1, 2), set("b", "c"), p(4, 3));
		aut.addTransition(p(1, 2), set("a", "b", "c"), p(4, 3));
		aut.addTransition(p(1, 2), set("a", "b", "c"), p(7, 3));
		aut.addTransition(p(2, 1), set(), p(4, 1));
		aut.addTransition(p(2, 1), set("a"), p(2, 1));
		aut.addTransition(p(2, 1), set("a"), p(4, 1));
		aut.addTransition(p(2, 1), set("b"), p(0, 1));
		aut.addTransition(p(2, 1), set("b"), p(4, 1));
		aut.addTransition(p(2, 1), set("c"), p(1, 1));
		aut.addTransition(p(2, 1), set("c"), p(4, 1));
		aut.addTransition(p(2, 1), set("a", "b"), p(4, 1));
		aut.addTransition(p(2, 1), set("a", "b"), p(5, 1));
		aut.addTransition(p(2, 1), set("a", "c"), p(4, 1));
		aut.addTransition(p(2, 1), set("a", "c"), p(6, 1));
		aut.addTransition(p(2, 1), set("b", "c"), p(3, 1));
		aut.addTransition(p(2, 1), set("b", "c"), p(4, 1));
		aut.addTransition(p(2, 1), set("a", "b", "c"), p(4, 1));
		aut.addTransition(p(2, 1), set("a", "b", "c"), p(7, 1));
		aut.addTransition(p(0, 3), set(), p(4, 3));
		aut.addTransition(p(0, 3), set("a"), p(2, 3));
		aut.addTransition(p(0, 3), set("a"), p(4, 3));
		aut.addTransition(p(0, 3), set("b"), p(0, 3));
		aut.addTransition(p(0, 3), set("b"), p(4, 3));
		aut.addTransition(p(0, 3), set("c"), p(1, 3));
		aut.addTransition(p(0, 3), set("c"), p(4, 3));
		aut.addTransition(p(0, 3), set("a", "b"), p(4, 3));
		aut.addTransition(p(0, 3), set("a", "b"), p(5, 3));
		aut.addTransition(p(0, 3), set("a", "c"), p(4, 3));
		aut.addTransition(p(0, 3), set("a", "c"), p(6, 3));
		aut.addTransition(p(0, 3), set("b", "c"), p(3, 3));
		aut.addTransition(p(0, 3), set("b", "c"), p(4, 3));
		aut.addTransition(p(0, 3), set("a", "b", "c"), p(4, 3));
		aut.addTransition(p(0, 3), set("a", "b", "c"), p(7, 3));
		aut.addTransition(p(2, 2), set(), p(4, 2));
		aut.addTransition(p(2, 2), set("a"), p(2, 2));
		aut.addTransition(p(2, 2), set("a"), p(4, 2));
		aut.addTransition(p(2, 2), set("b"), p(0, 2));
		aut.addTransition(p(2, 2), set("b"), p(4, 2));
		aut.addTransition(p(2, 2), set("c"), p(1, 2));
		aut.addTransition(p(2, 2), set("c"), p(4, 2));
		aut.addTransition(p(2, 2), set("a", "b"), p(4, 2));
		aut.addTransition(p(2, 2), set("a", "b"), p(5, 2));
		aut.addTransition(p(2, 2), set("a", "c"), p(4, 2));
		aut.addTransition(p(2, 2), set("a", "c"), p(6, 2));
		aut.addTransition(p(2, 2), set("b", "c"), p(3, 2));
		aut.addTransition(p(2, 2), set("b", "c"), p(4, 2));
		aut.addTransition(p(2, 2), set("a", "b", "c"), p(4, 2));
		aut.addTransition(p(2, 2), set("a", "b", "c"), p(7, 2));
		aut.addTransition(p(3, 1), set(), p(4, 2));
		aut.addTransition(p(3, 1), set("a"), p(2, 2));
		aut.addTransition(p(3, 1), set("a"), p(4, 2));
		aut.addTransition(p(3, 1), set("b"), p(0, 2));
		aut.addTransition(p(3, 1), set("b"), p(4, 2));
		aut.addTransition(p(3, 1), set("c"), p(1, 2));
		aut.addTransition(p(3, 1), set("c"), p(4, 2));
		aut.addTransition(p(3, 1), set("a", "b"), p(4, 2));
		aut.addTransition(p(3, 1), set("a", "b"), p(5, 2));
		aut.addTransition(p(3, 1), set("a", "c"), p(4, 2));
		aut.addTransition(p(3, 1), set("a", "c"), p(6, 2));
		aut.addTransition(p(3, 1), set("b", "c"), p(3, 2));
		aut.addTransition(p(3, 1), set("b", "c"), p(4, 2));
		aut.addTransition(p(3, 1), set("a", "b", "c"), p(4, 2));
		aut.addTransition(p(3, 1), set("a", "b", "c"), p(7, 2));
		aut.addTransition(p(1, 3), set(), p(4, 3));
		aut.addTransition(p(1, 3), set("a"), p(2, 3));
		aut.addTransition(p(1, 3), set("a"), p(4, 3));
		aut.addTransition(p(1, 3), set("b"), p(0, 3));
		aut.addTransition(p(1, 3), set("b"), p(4, 3));
		aut.addTransition(p(1, 3), set("c"), p(1, 3));
		aut.addTransition(p(1, 3), set("c"), p(4, 3));
		aut.addTransition(p(1, 3), set("a", "b"), p(4, 3));
		aut.addTransition(p(1, 3), set("a", "b"), p(5, 3));
		aut.addTransition(p(1, 3), set("a", "c"), p(4, 3));
		aut.addTransition(p(1, 3), set("a", "c"), p(6, 3));
		aut.addTransition(p(1, 3), set("b", "c"), p(3, 3));
		aut.addTransition(p(1, 3), set("b", "c"), p(4, 3));
		aut.addTransition(p(1, 3), set("a", "b", "c"), p(4, 3));
		aut.addTransition(p(1, 3), set("a", "b", "c"), p(7, 3));
		aut.addTransition(p(3, 2), set(), p(4, 3));
		aut.addTransition(p(3, 2), set("a"), p(2, 3));
		aut.addTransition(p(3, 2), set("a"), p(4, 3));
		aut.addTransition(p(3, 2), set("b"), p(0, 3));
		aut.addTransition(p(3, 2), set("b"), p(4, 3));
		aut.addTransition(p(3, 2), set("c"), p(1, 3));
		aut.addTransition(p(3, 2), set("c"), p(4, 3));
		aut.addTransition(p(3, 2), set("a", "b"), p(4, 3));
		aut.addTransition(p(3, 2), set("a", "b"), p(5, 3));
		aut.addTransition(p(3, 2), set("a", "c"), p(4, 3));
		aut.addTransition(p(3, 2), set("a", "c"), p(6, 3));
		aut.addTransition(p(3, 2), set("b", "c"), p(3, 3));
		aut.addTransition(p(3, 2), set("b", "c"), p(4, 3));
		aut.addTransition(p(3, 2), set("a", "b", "c"), p(4, 3));
		aut.addTransition(p(3, 2), set("a", "b", "c"), p(7, 3));
		aut.addTransition(p(4, 1), set(), p(4, 1));
		aut.addTransition(p(4, 1), set("a"), p(2, 1));
		aut.addTransition(p(4, 1), set("a"), p(4, 1));
		aut.addTransition(p(4, 1), set("b"), p(0, 1));
		aut.addTransition(p(4, 1), set("b"), p(4, 1));
		aut.addTransition(p(4, 1), set("c"), p(1, 1));
		aut.addTransition(p(4, 1), set("c"), p(4, 1));
		aut.addTransition(p(4, 1), set("a", "b"), p(4, 1));
		aut.addTransition(p(4, 1), set("a", "b"), p(5, 1));
		aut.addTransition(p(4, 1), set("a", "c"), p(4, 1));
		aut.addTransition(p(4, 1), set("a", "c"), p(6, 1));
		aut.addTransition(p(4, 1), set("b", "c"), p(3, 1));
		aut.addTransition(p(4, 1), set("b", "c"), p(4, 1));
		aut.addTransition(p(4, 1), set("a", "b", "c"), p(4, 1));
		aut.addTransition(p(4, 1), set("a", "b", "c"), p(7, 1));
		aut.addTransition(p(2, 3), set(), p(4, 1));
		aut.addTransition(p(2, 3), set("a"), p(2, 1));
		aut.addTransition(p(2, 3), set("a"), p(4, 1));
		aut.addTransition(p(2, 3), set("b"), p(0, 1));
		aut.addTransition(p(2, 3), set("b"), p(4, 1));
		aut.addTransition(p(2, 3), set("c"), p(1, 1));
		aut.addTransition(p(2, 3), set("c"), p(4, 1));
		aut.addTransition(p(2, 3), set("a", "b"), p(4, 1));
		aut.addTransition(p(2, 3), set("a", "b"), p(5, 1));
		aut.addTransition(p(2, 3), set("a", "c"), p(4, 1));
		aut.addTransition(p(2, 3), set("a", "c"), p(6, 1));
		aut.addTransition(p(2, 3), set("b", "c"), p(3, 1));
		aut.addTransition(p(2, 3), set("b", "c"), p(4, 1));
		aut.addTransition(p(2, 3), set("a", "b", "c"), p(4, 1));
		aut.addTransition(p(2, 3), set("a", "b", "c"), p(7, 1));
		aut.addTransition(p(4, 2), set(), p(4, 2));
		aut.addTransition(p(4, 2), set("a"), p(2, 2));
		aut.addTransition(p(4, 2), set("a"), p(4, 2));
		aut.addTransition(p(4, 2), set("b"), p(0, 2));
		aut.addTransition(p(4, 2), set("b"), p(4, 2));
		aut.addTransition(p(4, 2), set("c"), p(1, 2));
		aut.addTransition(p(4, 2), set("c"), p(4, 2));
		aut.addTransition(p(4, 2), set("a", "b"), p(4, 2));
		aut.addTransition(p(4, 2), set("a", "b"), p(5, 2));
		aut.addTransition(p(4, 2), set("a", "c"), p(4, 2));
		aut.addTransition(p(4, 2), set("a", "c"), p(6, 2));
		aut.addTransition(p(4, 2), set("b", "c"), p(3, 2));
		aut.addTransition(p(4, 2), set("b", "c"), p(4, 2));
		aut.addTransition(p(4, 2), set("a", "b", "c"), p(4, 2));
		aut.addTransition(p(4, 2), set("a", "b", "c"), p(7, 2));
		aut.addTransition(p(5, 1), set(), p(4, 2));
		aut.addTransition(p(5, 1), set("a"), p(2, 2));
		aut.addTransition(p(5, 1), set("a"), p(4, 2));
		aut.addTransition(p(5, 1), set("b"), p(0, 2));
		aut.addTransition(p(5, 1), set("b"), p(4, 2));
		aut.addTransition(p(5, 1), set("c"), p(1, 2));
		aut.addTransition(p(5, 1), set("c"), p(4, 2));
		aut.addTransition(p(5, 1), set("a", "b"), p(4, 2));
		aut.addTransition(p(5, 1), set("a", "b"), p(5, 2));
		aut.addTransition(p(5, 1), set("a", "c"), p(4, 2));
		aut.addTransition(p(5, 1), set("a", "c"), p(6, 2));
		aut.addTransition(p(5, 1), set("b", "c"), p(3, 2));
		aut.addTransition(p(5, 1), set("b", "c"), p(4, 2));
		aut.addTransition(p(5, 1), set("a", "b", "c"), p(4, 2));
		aut.addTransition(p(5, 1), set("a", "b", "c"), p(7, 2));
		aut.addTransition(p(3, 3), set(), p(4, 3));
		aut.addTransition(p(3, 3), set("a"), p(2, 3));
		aut.addTransition(p(3, 3), set("a"), p(4, 3));
		aut.addTransition(p(3, 3), set("b"), p(0, 3));
		aut.addTransition(p(3, 3), set("b"), p(4, 3));
		aut.addTransition(p(3, 3), set("c"), p(1, 3));
		aut.addTransition(p(3, 3), set("c"), p(4, 3));
		aut.addTransition(p(3, 3), set("a", "b"), p(4, 3));
		aut.addTransition(p(3, 3), set("a", "b"), p(5, 3));
		aut.addTransition(p(3, 3), set("a", "c"), p(4, 3));
		aut.addTransition(p(3, 3), set("a", "c"), p(6, 3));
		aut.addTransition(p(3, 3), set("b", "c"), p(3, 3));
		aut.addTransition(p(3, 3), set("b", "c"), p(4, 3));
		aut.addTransition(p(3, 3), set("a", "b", "c"), p(4, 3));
		aut.addTransition(p(3, 3), set("a", "b", "c"), p(7, 3));
		aut.addTransition(p(5, 2), set(), p(4, 2));
		aut.addTransition(p(5, 2), set("a"), p(2, 2));
		aut.addTransition(p(5, 2), set("a"), p(4, 2));
		aut.addTransition(p(5, 2), set("b"), p(0, 2));
		aut.addTransition(p(5, 2), set("b"), p(4, 2));
		aut.addTransition(p(5, 2), set("c"), p(1, 2));
		aut.addTransition(p(5, 2), set("c"), p(4, 2));
		aut.addTransition(p(5, 2), set("a", "b"), p(4, 2));
		aut.addTransition(p(5, 2), set("a", "b"), p(5, 2));
		aut.addTransition(p(5, 2), set("a", "c"), p(4, 2));
		aut.addTransition(p(5, 2), set("a", "c"), p(6, 2));
		aut.addTransition(p(5, 2), set("b", "c"), p(3, 2));
		aut.addTransition(p(5, 2), set("b", "c"), p(4, 2));
		aut.addTransition(p(5, 2), set("a", "b", "c"), p(4, 2));
		aut.addTransition(p(5, 2), set("a", "b", "c"), p(7, 2));
		aut.addTransition(p(6, 1), set(), p(4, 1));
		aut.addTransition(p(6, 1), set("a"), p(2, 1));
		aut.addTransition(p(6, 1), set("a"), p(4, 1));
		aut.addTransition(p(6, 1), set("b"), p(0, 1));
		aut.addTransition(p(6, 1), set("b"), p(4, 1));
		aut.addTransition(p(6, 1), set("c"), p(1, 1));
		aut.addTransition(p(6, 1), set("c"), p(4, 1));
		aut.addTransition(p(6, 1), set("a", "b"), p(4, 1));
		aut.addTransition(p(6, 1), set("a", "b"), p(5, 1));
		aut.addTransition(p(6, 1), set("a", "c"), p(4, 1));
		aut.addTransition(p(6, 1), set("a", "c"), p(6, 1));
		aut.addTransition(p(6, 1), set("b", "c"), p(3, 1));
		aut.addTransition(p(6, 1), set("b", "c"), p(4, 1));
		aut.addTransition(p(6, 1), set("a", "b", "c"), p(4, 1));
		aut.addTransition(p(6, 1), set("a", "b", "c"), p(7, 1));
		aut.addTransition(p(4, 3), set(), p(4, 3));
		aut.addTransition(p(4, 3), set("a"), p(2, 3));
		aut.addTransition(p(4, 3), set("a"), p(4, 3));
		aut.addTransition(p(4, 3), set("b"), p(0, 3));
		aut.addTransition(p(4, 3), set("b"), p(4, 3));
		aut.addTransition(p(4, 3), set("c"), p(1, 3));
		aut.addTransition(p(4, 3), set("c"), p(4, 3));
		aut.addTransition(p(4, 3), set("a", "b"), p(4, 3));
		aut.addTransition(p(4, 3), set("a", "b"), p(5, 3));
		aut.addTransition(p(4, 3), set("a", "c"), p(4, 3));
		aut.addTransition(p(4, 3), set("a", "c"), p(6, 3));
		aut.addTransition(p(4, 3), set("b", "c"), p(3, 3));
		aut.addTransition(p(4, 3), set("b", "c"), p(4, 3));
		aut.addTransition(p(4, 3), set("a", "b", "c"), p(4, 3));
		aut.addTransition(p(4, 3), set("a", "b", "c"), p(7, 3));
		aut.addTransition(p(6, 2), set(), p(4, 3));
		aut.addTransition(p(6, 2), set("a"), p(2, 3));
		aut.addTransition(p(6, 2), set("a"), p(4, 3));
		aut.addTransition(p(6, 2), set("b"), p(0, 3));
		aut.addTransition(p(6, 2), set("b"), p(4, 3));
		aut.addTransition(p(6, 2), set("c"), p(1, 3));
		aut.addTransition(p(6, 2), set("c"), p(4, 3));
		aut.addTransition(p(6, 2), set("a", "b"), p(4, 3));
		aut.addTransition(p(6, 2), set("a", "b"), p(5, 3));
		aut.addTransition(p(6, 2), set("a", "c"), p(4, 3));
		aut.addTransition(p(6, 2), set("a", "c"), p(6, 3));
		aut.addTransition(p(6, 2), set("b", "c"), p(3, 3));
		aut.addTransition(p(6, 2), set("b", "c"), p(4, 3));
		aut.addTransition(p(6, 2), set("a", "b", "c"), p(4, 3));
		aut.addTransition(p(6, 2), set("a", "b", "c"), p(7, 3));
		aut.addTransition(p(7, 1), set(), p(4, 2));
		aut.addTransition(p(7, 1), set("a"), p(2, 2));
		aut.addTransition(p(7, 1), set("a"), p(4, 2));
		aut.addTransition(p(7, 1), set("b"), p(0, 2));
		aut.addTransition(p(7, 1), set("b"), p(4, 2));
		aut.addTransition(p(7, 1), set("c"), p(1, 2));
		aut.addTransition(p(7, 1), set("c"), p(4, 2));
		aut.addTransition(p(7, 1), set("a", "b"), p(4, 2));
		aut.addTransition(p(7, 1), set("a", "b"), p(5, 2));
		aut.addTransition(p(7, 1), set("a", "c"), p(4, 2));
		aut.addTransition(p(7, 1), set("a", "c"), p(6, 2));
		aut.addTransition(p(7, 1), set("b", "c"), p(3, 2));
		aut.addTransition(p(7, 1), set("b", "c"), p(4, 2));
		aut.addTransition(p(7, 1), set("a", "b", "c"), p(4, 2));
		aut.addTransition(p(7, 1), set("a", "b", "c"), p(7, 2));
		aut.addTransition(p(5, 3), set(), p(4, 1));
		aut.addTransition(p(5, 3), set("a"), p(2, 1));
		aut.addTransition(p(5, 3), set("a"), p(4, 1));
		aut.addTransition(p(5, 3), set("b"), p(0, 1));
		aut.addTransition(p(5, 3), set("b"), p(4, 1));
		aut.addTransition(p(5, 3), set("c"), p(1, 1));
		aut.addTransition(p(5, 3), set("c"), p(4, 1));
		aut.addTransition(p(5, 3), set("a", "b"), p(4, 1));
		aut.addTransition(p(5, 3), set("a", "b"), p(5, 1));
		aut.addTransition(p(5, 3), set("a", "c"), p(4, 1));
		aut.addTransition(p(5, 3), set("a", "c"), p(6, 1));
		aut.addTransition(p(5, 3), set("b", "c"), p(3, 1));
		aut.addTransition(p(5, 3), set("b", "c"), p(4, 1));
		aut.addTransition(p(5, 3), set("a", "b", "c"), p(4, 1));
		aut.addTransition(p(5, 3), set("a", "b", "c"), p(7, 1));
		aut.addTransition(p(7, 2), set(), p(4, 3));
		aut.addTransition(p(7, 2), set("a"), p(2, 3));
		aut.addTransition(p(7, 2), set("a"), p(4, 3));
		aut.addTransition(p(7, 2), set("b"), p(0, 3));
		aut.addTransition(p(7, 2), set("b"), p(4, 3));
		aut.addTransition(p(7, 2), set("c"), p(1, 3));
		aut.addTransition(p(7, 2), set("c"), p(4, 3));
		aut.addTransition(p(7, 2), set("a", "b"), p(4, 3));
		aut.addTransition(p(7, 2), set("a", "b"), p(5, 3));
		aut.addTransition(p(7, 2), set("a", "c"), p(4, 3));
		aut.addTransition(p(7, 2), set("a", "c"), p(6, 3));
		aut.addTransition(p(7, 2), set("b", "c"), p(3, 3));
		aut.addTransition(p(7, 2), set("b", "c"), p(4, 3));
		aut.addTransition(p(7, 2), set("a", "b", "c"), p(4, 3));
		aut.addTransition(p(7, 2), set("a", "b", "c"), p(7, 3));
		aut.addTransition(p(6, 3), set(), p(4, 1));
		aut.addTransition(p(6, 3), set("a"), p(2, 1));
		aut.addTransition(p(6, 3), set("a"), p(4, 1));
		aut.addTransition(p(6, 3), set("b"), p(0, 1));
		aut.addTransition(p(6, 3), set("b"), p(4, 1));
		aut.addTransition(p(6, 3), set("c"), p(1, 1));
		aut.addTransition(p(6, 3), set("c"), p(4, 1));
		aut.addTransition(p(6, 3), set("a", "b"), p(4, 1));
		aut.addTransition(p(6, 3), set("a", "b"), p(5, 1));
		aut.addTransition(p(6, 3), set("a", "c"), p(4, 1));
		aut.addTransition(p(6, 3), set("a", "c"), p(6, 1));
		aut.addTransition(p(6, 3), set("b", "c"), p(3, 1));
		aut.addTransition(p(6, 3), set("b", "c"), p(4, 1));
		aut.addTransition(p(6, 3), set("a", "b", "c"), p(4, 1));
		aut.addTransition(p(6, 3), set("a", "b", "c"), p(7, 1));
		aut.addTransition(p(7, 3), set(), p(4, 1));
		aut.addTransition(p(7, 3), set("a"), p(2, 1));
		aut.addTransition(p(7, 3), set("a"), p(4, 1));
		aut.addTransition(p(7, 3), set("b"), p(0, 1));
		aut.addTransition(p(7, 3), set("b"), p(4, 1));
		aut.addTransition(p(7, 3), set("c"), p(1, 1));
		aut.addTransition(p(7, 3), set("c"), p(4, 1));
		aut.addTransition(p(7, 3), set("a", "b"), p(4, 1));
		aut.addTransition(p(7, 3), set("a", "b"), p(5, 1));
		aut.addTransition(p(7, 3), set("a", "c"), p(4, 1));
		aut.addTransition(p(7, 3), set("a", "c"), p(6, 1));
		aut.addTransition(p(7, 3), set("b", "c"), p(3, 1));
		aut.addTransition(p(7, 3), set("b", "c"), p(4, 1));
		aut.addTransition(p(7, 3), set("a", "b", "c"), p(4, 1));
		aut.addTransition(p(7, 3), set("a", "b", "c"), p(7, 1));

		aut.setInitial(p(0, 1));

		aut.setAccepting(p(0, 1));
		aut.setAccepting(p(3, 1));
		aut.setAccepting(p(5, 1));
		aut.setAccepting(p(7, 1));

		return aut;

	}

}