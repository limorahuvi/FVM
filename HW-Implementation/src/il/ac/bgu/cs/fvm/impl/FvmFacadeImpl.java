package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.channelsystem.ParserBasedInterleavingActDef;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.StmtContext;
import il.ac.bgu.cs.fvm.programgraph.*;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationFailed;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import java.io.InputStream;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import il.ac.bgu.cs.fvm.verification.VerificationSucceeded;
import org.antlr.v4.runtime.tree.ParseTree;
/**
 * Implement the methods in this class. You may add additional classes as you
 * want, as long as they live in the {@code impl} package, or one of its 
 * sub-packages.
 */
public class FvmFacadeImpl implements FvmFacade {

    @Override
    public <S, A, P> TransitionSystem<S, A, P> createTransitionSystem() {
        return new TransitionSystemImp<>();
    }

    @Override
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
        Set<S> init_set=ts.getInitialStates();
        int size_set_init=init_set.size();
        if(size_set_init<=1){
            Set<S> states=ts.getStates();
            Set<A> actions=ts.getActions();
           return isActionDeterministic_help(actions,states,ts);
        }
        else
            return false;
    }

    
    private <S, A, P> boolean isActionDeterministic_help(Set<A> actions, Set<S> states,TransitionSystem<S, A, P> ts) {
    	  for (A action :actions) {
              for (S state :states) {
                  Set<S> post_set=post(ts, state, action);
                  int size_post=post_set.size();
                  if (size_post > 1) {
                     return false;
                 }
             }
         }
		return true;
	}

	@Override
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {

    	Set<S> init_set=ts.getInitialStates();
		int size_set_init=init_set.size();
		if(size_set_init<=1){
        Set<S> states=ts.getStates();
        return isAPDeterministic_post(states,ts);
     
		}
		else
			return false;
    }
    
    private <S, A, P> boolean isAPDeterministic_post(Set<S> states, TransitionSystem<S, A, P> ts) {
    		int same=0;
    	   for(S state: states) {
               Set<S> post_ts = post(ts, state);
               Collection<Set<P>> labels_value= ts.getLabelingFunction().values();
               for(Set<P> labels : labels_value) {
                   for(S s_post : post_ts) {
                       if(isAPDeterministicHelp(ts,labels,s_post)){
                           same++;
                           if(same >1)
                               return false;
                       }
                   }
                   same=0;
               }
           }
		return true;
	}

	private <S, A, P> boolean isAPDeterministicHelp(TransitionSystem<S, A, P> ts, Set<P> labels, S s_post){
        if(ts.getLabel(s_post).containsAll(labels)){
        	if(labels.containsAll(ts.getLabel(s_post))) {
            return true;
        	}
            else{
            	return false;
            }
        }
        return false;
    }
    

    @Override
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if(isInitialExecutionFragment(ts, e)){
        	if(isMaximalExecutionFragment(ts, e)){
            return true;
        	}
        	else{
        		return false;
        	}
        }
        return false;
    }

    @Override
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        AlternatingSequence<S, A> temp=e;
        while(temp.size()>1) {
            check_state_exist(ts,temp.head());
            check_action_exist(ts,temp.tail().head());
            if(!isLegalTransition(ts,temp))
                return false;
            temp = temp.tail().tail();
        }
        S from = temp.head();
        check_state_exist(ts,from);
        return true;

    }

    private <S, A, P> boolean isLegalTransition(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> temp) {
        A action=temp.tail().head();
        S from = temp.head();
        S to=temp.tail().tail().head();
        Set<Transition<S, A>> transitions=ts.getTransitions();
        for(Transition<S, A> transition : transitions) {
            if(transition.getFrom().equals(from))
            	if(transition.getAction().equals(action))
                    if( transition.getTo().equals(to))
                return true;
        }
        return false;
    }

    @Override
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if(isExecutionFragment(ts, e)){
            S head=e.head();
            if(ts.getInitialStates().contains(head)){
                return true;
            }
            return false;
        }
        return false;
    }

    @Override
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if(isExecutionFragment(ts, e)){
            S last=e.last();
            if(isStateTerminal(ts, last)){
                return true;
            }
            return false;
        }
        return false;
    }
    
    @Override
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
        check_state_exist(ts,s);
        Set<S> posts=post(ts,s);
        if(posts.size()==0){
            return true;
        }
        return false;
    }
       
    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
        check_state_exist(ts, s);
        Set<S> post_set=new HashSet<S>();
        for(Transition<S, ?> transition : ts.getTransitions()) {
            S fromS=transition.getFrom();
            post_help1(transition,post_set,fromS,s);
        }
        return post_set;
    }

    private <S> void post_help1(Transition<S, ?> transition, Set<S> post_set,S fromS,S s) {
    	 if(fromS.equals(s)){
             S Tos=transition.getTo();
             post_set.add(Tos);
         }	
	}

	@Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
		check_state_exist_set(c,ts);
       
        Set<S> post_set = new HashSet<S>();
        for(Transition<S, ?> transition : ts.getTransitions()) {
            S fromS=transition.getFrom();
            post_help2(transition,post_set,fromS,c);
        }
        return post_set;
    }

   

	private <S> void post_help2(Transition<S, ?> transition, Set<S> post_set, S fromS,Set<S> c) {
    	  if(c.contains(fromS))
          {
              S Tos=transition.getTo();
              post_set.add(Tos);
          }
	}

	@Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
        check_action_exist(ts,a);
        check_state_exist(ts, s);
        Set<S> post_set = new HashSet<S>();
        for(Transition<S, A> transition : ts.getTransitions() ) {
            S fromS=transition.getFrom();
            post_help3(fromS,transition,a,post_set,s);
        }
        return post_set;
    }

    private <S,A> void post_help3(S fromS, Transition<S, A> transition, A a, Set<S> post_set,S s) {	
    	 if(fromS.equals(s))
    		if(transition.getAction().equals(a))
         {
             S Tos=transition.getTo();
             post_set.add(Tos);
         }
	}

	@Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        check_action_exist(ts,a);
        Set<S> states =ts.getStates();
        check_state_exist_set(states,ts);
        Set<S> post_set = new HashSet<S>();
        for(Transition<S, A> transition : ts.getTransitions()) {
            S fromS=transition.getFrom();
            post_help4(fromS,c,transition,a,post_set);
          
        }
        return post_set;
    }
    
    private <S,A> void post_help4(S fromS, Set<S> c, Transition<S, A> transition, A a, Set<S> post_set) {
		
    	  if(c.contains(fromS))
    		  if(transition.getAction().equals(a))
          {
              S Tos=transition.getTo();
              post_set.add(Tos);
          }
	}

	private <S,A> void check_state_exist_set(Set<S> states, TransitionSystem<S, A, ?> ts) {
		
    	  for(S state :states) {
              check_state_exist(ts, state);
          }
	}

	@Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        check_state_exist(ts, s);
        Set<S> pre_set=new HashSet<S>();
        for(Transition<S, ?> transition : ts.getTransitions()) {
            S Tos=transition.getTo();
            pre_help1(transition,pre_set,Tos,s);
           
        }
        return pre_set;
    }

    private <S> void pre_help1(Transition<S, ?> transition, Set<S> pre_set, S Tos, S s) {		
    	 if(Tos.equals(s)){
             S fromS=transition.getFrom();
             pre_set.add(fromS);
         }
	}

	@Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
		check_state_exist_set(c, ts);
        Set<S> pre_set = new HashSet<S>();
        for(Transition<S, ?> transition : ts.getTransitions()) {
            S Tos=transition.getTo();
            pre_help2(Tos,c,pre_set,c,transition);
        }
        return pre_set;
    }

    private <S> void pre_help2(S tos, Set<S> c, Set<S> pre_set, Set<S> c2,Transition<S, ?> transition) {
    	  if(c.contains(tos))
          {
              S fromS=transition.getFrom();
              pre_set.add(fromS);
          }
	}

	@Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {

        check_action_exist(ts,a);
        check_state_exist(ts, s);
        Set<S> pre_set = new HashSet<S>();
        for(Transition<S, A> transition : ts.getTransitions() ) {
            S ToS=transition.getTo();
            pre_help3(ToS,s,a,pre_set,transition);
        }
        return pre_set;
    }

    private <S,A> void pre_help3(S toS, S s, A a, Set<S> pre_set, Transition<S, A> transition) {
	
    	 if(toS.equals(s))
    		 if(transition.getAction().equals(a))
         {
             S fromS=transition.getFrom();
             pre_set.add(fromS);
         }
	}

	@Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        check_action_exist(ts,a);
        Set<S> states =ts.getStates();
        check_state_exist_set(states, ts);
        Set<S> pre_set = new HashSet<S>();
        for(Transition<S, A> transition : ts.getTransitions()) {
            S Tos=transition.getTo();
            pre_help4(c,Tos,transition,a,pre_set);
        }
        return pre_set;
    }

    private <S,A> void pre_help4(Set<S> c, S tos, Transition<S, A> transition, A a, Set<S> pre_set) {
		
    	  if(c.contains(tos))
    		  if(transition.getAction().equals(a))
          {
              S fromS=transition.getFrom();
              pre_set.add(fromS);
          }
	}

	@Override
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {

        Set<S> reach_states = new HashSet<S>();
        reach_help(reach_states,ts);
        boolean found = true;
        boolean isAdded = false;
        reach_help_add(found,isAdded,reach_states,ts);
        return reach_states;
    }

    private <S, A> void reach_help_add(boolean found, boolean isAdded, Set<S> reach_states, TransitionSystem<S, A, ?> ts) {
    	   while(found ==true) {
               found = false;
               Set<Transition<S, A>> ts_transitions=ts.getTransitions();
               for(Transition<S, A> transition :ts_transitions) {
                   isAdded = false;
                   if(reach_help_contains(transition,reach_states)){
                	   found=true;
                   }
               }
           }
	}

	private<S,A > boolean reach_help_contains(Transition<S, A> transition, Set<S> reach_states) {
		
		 S fromS=transition.getFrom();
		 if(reach_states.contains(fromS)) {
             S getS=transition.getTo();
            boolean isAdded = reach_states.add(getS);
             if(isAdded)
                 return true;
         }
		 return false;
		
	}

	private <S, A> void reach_help(Set<S> reach_states, TransitionSystem<S, A, ?> ts) {

        for(S state : ts.getInitialStates()) {
            reach_states.add(state);
        }
    }
     
    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2) {
        Set<A> handShakingActions = Collections.emptySet();
        return interleave(ts1, ts2, handShakingActions);
    }

    private <S1,S2> Set<Pair<S1, S2>>  interleaveStates(Set<S1> states1, Set<S2> states2){
        Set<Pair<S1, S2>> states = new HashSet<>();
        for (S1 s1: states1) {
            for(S2 s2: states2){
                states.add(Pair.pair(s1,s2));
            }
        }
        return states;
    }

    private <T> Set<T> union (Set<T> s1, Set<T> s2){
        Set<T> unioned = Stream.concat(s1.stream(), s2.stream()).collect(Collectors.toSet());
        return unioned;
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        Set<Pair<S1, S2>>  interleaveInitialStates = interleaveStates(ts1.getInitialStates(), ts2.getInitialStates());
        Set<Pair<S1, S2>>  interleaveStates = interleaveStates(ts1.getStates(), ts2.getStates());
        Set<A> actions = union(ts1.getActions(), ts2.getActions());

        Set<Transition<Pair<S1, S2>,A>> transitions = getTransitionsWithoutHandShaking(ts1.getTransitions(), interleaveStates, handShakingActions, true);
        transitions = union(transitions, getTransitionsWithoutHandShaking(ts2.getTransitions(), interleaveStates, handShakingActions, false));
        transitions = union(transitions, getTransitionsWithHandShaking(ts1.getTransitions(), ts2.getTransitions(), handShakingActions));

        Set<P> atomicPropositions = union(ts1.getAtomicPropositions(), ts2.getAtomicPropositions());

        TransitionSystem<Pair<S1, S2>, A, P> newTS = createTransitionSystem(interleaveInitialStates, interleaveStates, actions, transitions, atomicPropositions);

        removeUnreachables(newTS);

        interleaveLabels(newTS, ts1, ts2);

        return newTS;
    }

    private <A, S2, S1, P> void removeUnreachables(TransitionSystem<Pair<S1,S2>,A,P> ts) {
        Set<Pair<S1,S2>> reachablesStates = reach(ts);
        Set<Pair<S1,S2>> unreachablesStates = new HashSet<>();
        for(Pair<S1,S2> s:ts.getStates()){
            if(!reachablesStates.contains(s)){
                unreachablesStates.add(s);
            }
        }
        Set<Transition<Pair<S1,S2>, A>> unreachablesTransitions = new HashSet<>();
        for(Transition<Pair<S1,S2>, A> t : ts.getTransitions()){
            for(Pair<S1,S2> s : unreachablesStates){
                if(t.getFrom().equals(s)||t.getTo().equals(s)){
                    unreachablesTransitions.add(t);
                }
            }
        }

        for(Transition<Pair<S1,S2>, A> t : unreachablesTransitions){
            ts.removeTransition(t);
        }

        for(Pair<S1,S2> s : unreachablesStates){
            ts.removeState(s);
        }

    }

    private <P, S1, S2, A> void interleaveLabels(TransitionSystem<Pair<S1,S2>,A,P> newTS, TransitionSystem<S1,A,P> ts1, TransitionSystem<S2,A,P> ts2) {
        for(Pair<S1,S2> s : newTS.getStates()) {
            for (P label : ts1.getLabel(s.getFirst())) {
                newTS.addToLabel(s, label);
            }
            for (P label : ts2.getLabel(s.getSecond())) {
                newTS.addToLabel(s, label);
            }
        }
    }

    private <S2, P, A, S1> TransitionSystem<Pair<S1,S2>,A,P> createTransitionSystem(Set<Pair<S1,S2>> interleaveInitialStates, Set<Pair<S1,S2>> interleaveStates, Set<A> actions, Set<Transition<Pair<S1,S2>,A>> transitions, Set<P> atomicPropositions) {
        TransitionSystem<Pair<S1, S2>, A, P> ts = createTransitionSystem();
        ts.addAllStates(interleaveStates);
        for(Pair<S1,S2> s : interleaveInitialStates){
            ts.setInitial(s, true);
        }
        ts.addAllActions(actions);
        ts.addAllAtomicPropositions(atomicPropositions);
        for (Transition<Pair<S1,S2>,A> t:transitions) {
            ts.addTransition(t);

        }
        return ts;
    }

    private <A, S1, S2> Set<Transition<Pair<S1, S2>,A>> getTransitionsWithHandShaking(Set<Transition<S1,A>> transitions1, Set<Transition<S2,A>> transitions2, Set<A> handShakingActions) {
        Set<Transition<Pair<S1, S2>,A>> transitions = new HashSet<>();
        for(A a : handShakingActions){
            for(Transition<S1,A> t1: transitions1){
                for(Transition<S2,A> t2: transitions2){
                    if(t1.getAction().equals(a) && t2.getAction().equals(a)){
                        transitions.add(new Transition<>(Pair.pair(t1.getFrom(), t2.getFrom()), a, Pair.pair(t1.getTo(), t2.getTo())));
                    }
                }
            }
        }
        return transitions;
    }

    private <A, S1,S2, S> Set<Transition<Pair<S1, S2>,A>> getTransitionsWithoutHandShaking(Set<Transition<S,A>> transitionsFromTS, Set<Pair<S1,S2>> interleaveStates, Set<A> handShakingActions, boolean isFirstInStatePair) {
        Set<Transition<Pair<S1, S2>,A>> transitions = new HashSet<>();
        Set<Transition<S,A>> notHandShakingTransition = new HashSet<>();
        for(Transition<S,A> t : transitionsFromTS){
            if(!handShakingActions.contains(t.getAction())){
                notHandShakingTransition.add(t);
            }
        }
        for(Transition<S,A> t: notHandShakingTransition){
            for(Pair<S1,S2> s1: interleaveStates){
                for(Pair<S1,S2> s2: interleaveStates){
                    if((isFirstInStatePair && t.getFrom().equals(s1.getFirst()) && t.getTo().equals(s2.getFirst()) && s1.getSecond().equals(s2.getSecond()))||
                            (!isFirstInStatePair && t.getFrom().equals(s1.getSecond()) && t.getTo().equals(s2.getSecond()) && s1.getFirst().equals(s2.getFirst()))){
                        transitions.add(new Transition<>(s1, t.getAction(), s2));
                    }
                }
            }
        }
        return transitions;
    }

    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        return new ProgramGraphImpl<>();
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        Set<Pair<L1,L2>> locations_init = interleaveStates(pg1.getInitialLocations(), pg2.getInitialLocations());
        Set<Pair<L1,L2>> locations = interleaveStates(pg1.getLocations(), pg2.getLocations());
        Set<List<String>> initialstates = interleaveInitPG(pg1.getInitalizations(), pg2.getInitalizations());
        Set<PGTransition<Pair<L1,L2>, A>> p_transitions = getTransitionsForPG(pg1.getTransitions(),locations, true);
        p_transitions = union(p_transitions,getTransitionsForPG(pg2.getTransitions(),locations, false));
        ProgramGraph<Pair<L1,L2>,A> pg = createProgramGraph(locations_init, locations,initialstates,p_transitions);
        return pg;
    }

    private Set<List<String>> interleaveInitPG(Set<List<String>> init1, Set<List<String>> init2) {
        Set<List<String>> init = new HashSet<>();
        for(List<String> i1 : init1){
            for(List<String> i2 : init2){
                init.add(Stream.concat(i1.stream(), i2.stream()).collect(Collectors.toList()));
            }

        }
        return init;
    }

    private <L2, A, L1> ProgramGraph<Pair<L1,L2>,A> createProgramGraph(Set<Pair<L1,L2>> locations_init, Set<Pair<L1,L2>> locations, Set<List<String>> initialstates, Set<PGTransition<Pair<L1,L2>,A>> p_transitions) {
        ProgramGraph<Pair<L1,L2>,A> pg = createProgramGraph();
        for(Pair<L1,L2> l : locations){
            pg.addLocation(l);
        }
        for(Pair<L1,L2> l : locations_init){
            pg.setInitial(l, true);
        }
        for(List<String> l : initialstates){
            pg.addInitalization(l);
        }
        for(PGTransition<Pair<L1,L2>,A> l : p_transitions){
            pg.addTransition(l);
        }


        return pg;
    }

    private <L2, A, L1, L> Set<PGTransition<Pair<L1,L2>,A>> getTransitionsForPG(Set<PGTransition<L,A>> transitions, Set<Pair<L1,L2>> locations, boolean isFirstInStatePair) {
        Set<PGTransition<Pair<L1,L2>,A>> interleaved_transitions = new HashSet<>();

        for(PGTransition<L,A> t: transitions){
            for(Pair<L1,L2> s1: locations){
                for(Pair<L1,L2> s2: locations){
                    if((isFirstInStatePair && t.getFrom().equals(s1.getFirst()) && t.getTo().equals(s2.getFirst()) && s1.getSecond().equals(s2.getSecond()))||
                            (!isFirstInStatePair && t.getFrom().equals(s1.getSecond()) && t.getTo().equals(s2.getSecond()) && s1.getFirst().equals(s2.getFirst()))){
                        interleaved_transitions.add(new PGTransition<>(s1,t.getCondition(), t.getAction(), s2));
                    }
                }
            }
        }
        return interleaved_transitions;


    }

    @Override
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(Circuit c) {
        TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transition_system_ans = createTransitionSystem();


        help_ts_from_circuit( transition_system_ans, c);

        add_atomic_p_help(transition_system_ans,c);

        add_transition_help(transition_system_ans,c);

        reachable_and_unreachable_help(transition_system_ans);

        help_ts_from_circuit2(transition_system_ans,c);

        return transition_system_ans;
    }

    private void help_ts_from_circuit2(
            TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transition_system_ans,Circuit c) {



        for(Pair<Map<String, Boolean>, Map<String, Boolean>> s :transition_system_ans.getStates()){
            {
                Set<Map.Entry<String,Boolean>> set2=Stream.concat(s.getSecond().entrySet().stream(), c.computeOutputs(s.getFirst(), s.getSecond()).entrySet().stream()).collect(Collectors.toSet());
                Set<Map.Entry<String,Boolean>> set1=Stream.concat(s.getFirst().entrySet().stream(), set2.stream()).collect(Collectors.toSet());
                ArrayList<Map.Entry<String,Boolean>> arr=new ArrayList<>();
                for(Map.Entry<String,Boolean> t:set1){
                    if(t.getValue()){
                        arr.add(t);
                    }
                }
                ArrayList<String> keys=new ArrayList<>();
                Set<Map.Entry<String,Boolean>> set_value=arr.stream().collect(Collectors.toSet());
                for(Map.Entry<String,Boolean> element:set_value){
                    keys.add(element.getKey());
                }
                Set<String> set1_update=keys.stream().collect(Collectors.toSet());
                for(String t:set1_update){
                    transition_system_ans.addToLabel(s, t);
                }
            }
        }
    }

    private void add_transition_help(
            TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transition_system_ans,
            Circuit c) {

        for(Pair<Map<String, Boolean>, Map<String, Boolean>> s1 : transition_system_ans.getStates()){
            for(Pair<Map<String, Boolean>, Map<String, Boolean>> s2 : transition_system_ans.getStates()){
                Map<String, Boolean> first_s1=s1.getFirst();
                Map<String, Boolean> second_s1=s1.getSecond();
                Map<String, Boolean> c_update_reg=c.updateRegisters(first_s1, second_s1);
                Map<String, Boolean> second_s2=s2.getSecond();
                if (c_update_reg.equals(second_s2)) {
                    Map<String, Boolean> first_s2=s2.getFirst();
                    transition_system_ans.addTransition(new Transition<>(s1, first_s2, s2));
                }
            }
        }

    }

    private void reachable_and_unreachable_help(
            TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transition_system_ans) {



        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> reach_states = reach(transition_system_ans);
        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> un_reach;

        ArrayList<Pair<Map<String, Boolean>, Map<String, Boolean>>> arr=new ArrayList<>();
        for(Pair<Map<String, Boolean>, Map<String, Boolean>> s:transition_system_ans.getStates())
        {

            if(!reach_states.contains(s)){
                arr.add(s);
            }
        }
        un_reach=arr.stream().collect(Collectors.toSet());

        Set<Transition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>>> unreachableTransitions ;
        ArrayList<Transition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>>> arr_trans=new ArrayList<>();
        for(Transition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>> t: transition_system_ans.getTransitions())
        {

            if(un_reach.contains(t.getFrom())){
                arr_trans.add(t);
            }
        }
        unreachableTransitions=arr_trans.stream().collect(Collectors.toSet());
        for(Transition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>> ur_t :unreachableTransitions){
            transition_system_ans.removeTransition(ur_t);
        }
        for(Pair<Map<String, Boolean>, Map<String, Boolean>> ur_s :un_reach){
            transition_system_ans.removeState(ur_s);
        }

    }

    private void add_atomic_p_help(
            TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transition_system_ans,Circuit c
    ) {

        List<String> regNames = new ArrayList<>(c.getRegisterNames());
        List<String> input_port_names = new ArrayList<>(c.getInputPortNames());
        List<String> output_port_names = new ArrayList<>(c.getOutputPortNames());

        Set<String> set1=Stream.concat(regNames.stream(), output_port_names.stream()).collect(Collectors.toSet());
        Set<String> set2 =Stream.concat(input_port_names.stream(), set1.stream()).collect(Collectors.toSet());
        for(String string_set2:set2){
            transition_system_ans.addAtomicProposition(string_set2);
        }
    }

    private void help_ts_from_circuit(TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transition_system_ans,Circuit c) {

        int input_size = c.getInputPortNames().size();
        int register_size = c.getRegisterNames().size();

        double input_pow = Math.pow(2, input_size);
        double register_pow = Math.pow(2, register_size);

        List<String> regNames = new ArrayList<>(c.getRegisterNames());
        List<String> inputPortNames = new ArrayList<>(c.getInputPortNames());

        for (int i = 0; i < input_pow; i++) {

            Map<String, Boolean> inputState = new HashMap<>();
            Boolean[] input_in_binary = to_binary(i, input_size);
            port_name_help(inputState,input_in_binary,inputPortNames);

            for (int j = 0; j < register_pow; j++) {
                Map<String, Boolean> registerState = new HashMap<>();
                Boolean[] reg_binary = to_binary(j, register_size);
                reg_help(registerState,reg_binary,regNames,input_in_binary);
                add_state_help(transition_system_ans,inputState,registerState,j);
            }
            transition_system_ans.addAction(inputState);
        }
    }

    private void reg_help(Map<String, Boolean> registerState, Boolean[] reg_binary, List<String> regNames,
                          Boolean[] input_in_binary) {
        int index_j;
        int binary_size_j=input_in_binary.length;
        for (index_j = 0; index_j < binary_size_j; index_j++) {
            String element_reg_name=regNames.get(index_j);
            Boolean element_binary_reg=reg_binary[index_j];
            registerState.put(element_reg_name, element_binary_reg);
        }

    }

    private void port_name_help(Map<String, Boolean> inputState, Boolean[] input_in_binary,
                                List<String> inputPortNames) {
        int index_i;
        int binary_size=input_in_binary.length;
        for (index_i = 0; index_i < binary_size; index_i=index_i+1) {
            String element_port_name=inputPortNames.get(index_i);
            Boolean element_binary=input_in_binary[index_i];
            inputState.put(element_port_name, element_binary);
        }

    }

    private void add_state_help(
            TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transition_system_ans,
            Map<String, Boolean> inputState, Map<String, Boolean> registerState, int j) {

        transition_system_ans.addState(Pair.pair(inputState, registerState));
        if (j == 0) {
            transition_system_ans.setInitial(Pair.pair(inputState, registerState),true);
        }

    }

    private Boolean[] to_binary(int number_to_binary, int size) {

        StringBuilder binaryStringBuilder = new StringBuilder(Integer.toBinaryString(number_to_binary));
        to_binaryhelp(binaryStringBuilder,size);
        String binaryString = binaryStringBuilder.toString();
        Boolean[] ans = new Boolean[size];
        return to_binaryhelp2(binaryString,ans,size);
    }

    private Boolean[] to_binaryhelp2(String binaryString, Boolean[] ans,int size) {

        for (int i = 0; i < size;i++) {
            if( binaryString.charAt(i) == '1')
                ans[i]=true;
            else
                ans[i]=false;
        }

        return ans;
    }

    private void to_binaryhelp(StringBuilder binaryStringBuilder,int size) {

        int size_for=(size - binaryStringBuilder.length());
        for (int i = 0; i < size_for; i++) {
            binaryStringBuilder.insert(0, "0");
        }

    }

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {

        TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystem_ans = createTransitionSystem();


        Set<Map<String, Object>> init_evals=init_vals_help(pg,actionDefs);

        if (init_evals.isEmpty()) {
            init_evals.add(new HashMap<>());
        }

        init_vals_help2(pg,init_evals,transitionSystem_ans);

        Set<Pair<L, Map<String, Object>>> states_set=transitionSystem_ans.getInitialStates();
        List<Pair<L, Map<String, Object>>> states = new ArrayList<>(states_set);
        while (!states.isEmpty()) {
            Pair<L, Map<String, Object>> fromState = states.get(0);
            states.remove(0);
            Set<PGTransition<L, A>> pg_trans_set=pg.getTransitions();
            for(PGTransition<L, A> t: pg_trans_set)
            {
                L t_from=t.getFrom();
                L t_first=fromState.getFirst();
                Map<String,Object> t_second=fromState.getSecond();
                String t_condition=t.getCondition();

                if (t_from.equals(t_first)){
                    for(ConditionDef c: conditionDefs){
                        if(c.evaluate(t_second, t_condition)){
                            Set<ActionDef>  matches_set=ad_matching_action(actionDefs,t);
                            if (matches_set.isEmpty()) {
                                matches_empty(fromState,transitionSystem_ans,states,t);
                            }

                            else {
                                matches_not_empty(matches_set,fromState,states,transitionSystem_ans,t);
                            }
                        }}}}}
        atomicp_lables(transitionSystem_ans);
        return transitionSystem_ans;
    }

    private <A, L> void atomicp_lables(TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystem_ans) {
        Set<Pair<L, Map<String, Object>>> states_set=transitionSystem_ans.getStates();
        for(Pair<L, Map<String, Object>> state: states_set){
            String state_string=state.getFirst().toString();
            transitionSystem_ans.addAtomicProposition(state_string);
            transitionSystem_ans.addToLabel(state,state_string);

            for(String second_state :state.getSecond().keySet()){
                String expression="";
                expression = second_state + " = " + state.getSecond().get(second_state);
                transitionSystem_ans.addAtomicProposition(expression);
                transitionSystem_ans.addToLabel(state, expression);
            }
        }
    }

    private <L, A> void matches_not_empty(Set<ActionDef> matches_set, Pair<L, Map<String, Object>> fromState,
                                          List<Pair<L, Map<String, Object>>> states,
                                          TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystem_ans, PGTransition<L, A> t) {

        for(ActionDef ad: matches_set){
            A action_t=t.getAction();
            L getTo_t=t.getTo();
            Map<String, Object> second_from=fromState.second;
            Map<String, Object> affect_ad=ad.effect(second_from, action_t);
            Pair<L, Map<String, Object>> toState = Pair.pair(getTo_t,affect_ad );
            Set<Pair<L, Map<String, Object>>> states_set =transitionSystem_ans.getStates();
            if (!states_set.contains(toState)) {
                transitionSystem_ans.addState(toState);
                states.add(toState);
            }
            transitionSystem_ans.addAction(action_t);
            transitionSystem_ans.addTransition(new Transition<>(fromState,action_t, toState));
        }
    }

    private <L, A> void matches_empty(Pair<L, Map<String, Object>> fromState,
                                      TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystem_ans,
                                      List<Pair<L, Map<String, Object>>> states, PGTransition<L, A> t) {

        A action_t=t.getAction();
        L getTo_t=t.getTo();
        Map<String, Object> second_from=fromState.getSecond();
        Pair<L, Map<String, Object>> toState = Pair.pair(getTo_t,second_from);
        Set<Pair<L, Map<String, Object>>> states_set =transitionSystem_ans.getStates();
        if (!states_set.contains(toState)) {
            transitionSystem_ans.addState(toState);
            states.add(toState);
        }
        transitionSystem_ans.addAction(action_t);
        transitionSystem_ans.addTransition(new Transition<>(fromState, action_t, toState));
    }

    private <L, A> Set<ActionDef> ad_matching_action(Set<ActionDef> actionDefs, PGTransition<L, A> t) {

        ArrayList<ActionDef> matches_arr=new ArrayList<>();
        A action_t=t.getAction();
        for(ActionDef ad: actionDefs){
            if(ad.isMatchingAction(action_t)){
                matches_arr.add(ad);
            }
        }
        return matches_arr.stream().collect(Collectors.toSet());
    }

    private <A, L> void init_vals_help2(ProgramGraph<L, A> pg, Set<Map<String, Object>> init_evals,
                                        TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystem_ans) {

        Set<L> pg_inits=pg.getInitialLocations();
        for(L pg_init :pg_inits){
            for(Map<String,Object> init_eval :init_evals){
                transitionSystem_ans.addState(Pair.pair(pg_init, init_eval));
                transitionSystem_ans.setInitial(Pair.pair(pg_init, init_eval),true);
            }
        }
    }

    private <L, A> Set<Map<String, Object>> init_vals_help(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs) {

        ArrayList<Map<String, Object>> arr=new ArrayList<>();
        Set<List<String>> pg_inits=pg.getInitalizations();
        for(List<String> element_set :pg_inits)
        {
            Map<String, Object> init_evals = new HashMap<>();
            ArrayList<ActionDef> arr_ad=new ArrayList<>();
            for (String s : element_set) {
                for(ActionDef ad:actionDefs){
                    if(ad.isMatchingAction(s)){
                        arr_ad.add(ad);
                    }
                }
                Set<ActionDef> ad_set= arr_ad.stream().collect(Collectors.toSet());
                for (ActionDef ad : ad_set) {
                    init_evals = ad.effect(init_evals, s);
                }
            }
            arr.add(init_evals);
        }

        return arr.stream().collect(Collectors.toSet());
    }

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {
        TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ts = createTransitionSystem();
        List<ProgramGraph<L,A>> pgs = cs.getProgramGraphs();
        Set<List<L>> initialLoc = getInitialLocFromPgs(pgs);
        Set<List<String>> initializations =  getInitializationsFromPgs(pgs);
        addStatesFromCS(ts, initialLoc, initializations, pgs);
        addApAndLables(ts);
        return ts;

    }

    private <L, A> void addApAndLables(TransitionSystem<Pair<List<L>, Map<String, Object>>,A, String> ts) {
        for(Pair<List<L>, Map<String, Object>> state : ts.getStates()){
            for(L l : state.first){
                String ap = l.toString();
                ts.addAtomicProposition(ap);
                ts.addToLabel(state, ap);
            }
            for(Map.Entry<String, Object> entry : state.second.entrySet()) {
                String key = entry.getKey();
                Object value = entry.getValue();
                String ap = key + " = " +value;
                ts.addAtomicProposition(ap);
                ts.addToLabel(state, ap);
            }
        }
    }

    private <A, L> void addStatesFromCS(TransitionSystem<Pair<List<L>, Map<String, Object>>,A, String> ts, Set<List<L>> initialLoc, Set<List<String>> initializations,List<ProgramGraph<L,A>> pgs) {
        addInitialStatesFromCS(ts, initialLoc, initializations);
        addNotInitialStatesFromCS(ts, pgs);
    }

    private <A, L> void addNotInitialStatesFromCS(TransitionSystem<Pair<List<L>, Map<String, Object>>,A, String> ts, List<ProgramGraph<L,A>> pgs) {
        Set<Pair<List<L>, Map<String, Object>>> checked = new HashSet<>();
        Set<Pair<List<L>, Map<String, Object>>> toCheck = new HashSet<>(ts.getInitialStates());
        Set<Pair<List<L>, Map<String, Object>>> toBeChecked;
        Map<String, Object> eval = null;

        while(!toCheck.isEmpty()){
            toBeChecked = new HashSet<>();
            for (Pair<List<L>, Map<String, Object>> fromState : toCheck) {
                checked.add(fromState);
                addStatesByTransitionsFromCS(pgs, ts, fromState, eval, checked, toBeChecked);
                List<List<PGTransition<L, A>>> transitionsByPgs = getTransitionsByPgsFromCS(pgs, fromState);
                Set<Transition<List<L>, A>> handshakes = getHandshakesFromCS(pgs, fromState, transitionsByPgs);
                addStatesFromHandshakesCS(ts, handshakes, eval, checked, toBeChecked, fromState);
            }
            toCheck = toBeChecked;
        }
    }

    private <A, L> void addStatesFromHandshakesCS(TransitionSystem<Pair<List<L>, Map<String, Object>>,A, String> ts, Set<Transition<List<L>,A>> handshakes, Map<String, Object> eval, Set<Pair<List<L>, Map<String, Object>>> checked, Set<Pair<List<L>, Map<String, Object>>> toBeChecked, Pair<List<L>, Map<String, Object>> fromState) {
        ParserBasedInterleavingActDef iad = new ParserBasedInterleavingActDef();
        for (Transition<List<L>, A> t : handshakes) {
            eval = iad.effect(fromState.getSecond(), t.getAction());
            if (eval != null) {
                Pair<List<L>, Map<String, Object>> newState = Pair.pair(t.getTo(), eval);
                if (!checked.contains(newState)) {
                    toBeChecked.add(newState);
                }
                ts.addState(newState);
                ts.addAction(t.getAction());
                ts.addTransition(new Transition<>(fromState, t.getAction(), newState));
            }
        }

    }

    private <A, L> Set<Transition<List<L>,A>> getHandshakesFromCS(List<ProgramGraph<L,A>> pgs, Pair<List<L>, Map<String, Object>> fromState, List<List<PGTransition<L, A>>> transitionsByPGS) {
        Set<Transition<List<L>,A>> handshakes = new HashSet<>();
        ParserBasedInterleavingActDef iad = new ParserBasedInterleavingActDef();
        int size = pgs.size();
        for(int i=0; i<size; i++){
            for(int j=0; j<size; j++){
                List<PGTransition<L, A>> transitions1 = transitionsByPGS.get(i);
                List<PGTransition<L, A>> transitions2 = transitionsByPGS.get(j);
                if(i!=j) {
                    for (PGTransition<L, A> t1 : transitions1) {
                        for (PGTransition<L, A> t2 : transitions2) {
                            String act = t1.getAction().toString() + "|" + t2.getAction().toString();
                            if (iad.isMatchingAction(act)) {
                                List<L> tmp = new ArrayList<>();
                                tmp.addAll(fromState.getFirst());
                                tmp.set(i, t1.getTo());
                                tmp.set(j, t2.getTo());
                                handshakes.add(new Transition<>(fromState.getFirst(), (A) act, tmp));
                            }
                        }
                    }
                }
            }
        }
        return handshakes;
    }

    private <A, L> List<List<PGTransition<L,A>>> getTransitionsByPgsFromCS(List<ProgramGraph<L,A>> pgs, Pair<List<L>, Map<String, Object>> fromState) {
        ParserBasedCondDef cd = new ParserBasedCondDef();
        List<List<PGTransition<L,A>>> trans = new ArrayList<>();
        List<PGTransition<L,A>> tempTrans = null;
        int size = pgs.size();
        for(int i=0; i<size; i++){
            tempTrans = new ArrayList<>();
            L loc = fromState.getFirst().get(i);
            for(PGTransition<L,A> t : pgs.get(i).getTransitions()){
                if(fromState.getSecond() != null &&
                        t.getFrom().equals(loc) &&
                        cd.evaluate(fromState.getSecond(), t.getCondition())){
                    tempTrans.add(t);
                }
            }
            trans.add(tempTrans);
        }
        return trans;
    }

    private <A, L> void addStatesByTransitionsFromCS(List<ProgramGraph<L,A>> pgs, TransitionSystem<Pair<List<L>, Map<String, Object>>,A, String> ts, Pair<List<L>, Map<String, Object>> fromState, Map<String, Object> eval, Set<Pair<List<L>, Map<String, Object>>> checked, Set<Pair<List<L>, Map<String, Object>>> toBeChecked) {
        ParserBasedActDef ad = new ParserBasedActDef();
        ParserBasedCondDef cd = new ParserBasedCondDef();
        ParserBasedInterleavingActDef iad = new ParserBasedInterleavingActDef();
        List<L> toState = null;
        Pair<List<L>, Map<String, Object>> newState = null;
        for (int i = 0; i < pgs.size(); i++) {
            Set<PGTransition<L, A>> transitions = pgs.get(i).getTransitions();
            for (PGTransition<L, A> trans : transitions) {
                if (fromState.getSecond() != null) {
                    if (fromState.getFirst().get(i).equals(trans.getFrom()) &&
                            cd.evaluate(fromState.getSecond(), trans.getCondition()) &&
                            !iad.isOneSidedAction(trans.getAction().toString())) {
                        eval = ad.effect(fromState.getSecond(), trans.getAction());
                        toState = new ArrayList<>();
                        toState.addAll(fromState.getFirst());
                        toState.set(i, trans.getTo());
                        newState = Pair.pair(toState, eval);
                        if (newState.getSecond() != null) {
                            if (!checked.contains(newState)) {
                                toBeChecked.add(newState);
                            }
                            ts.addState(newState);
                            ts.addAction(trans.getAction());
                            ts.addTransition(new Transition<>(fromState, trans.getAction(), newState));
                        }
                    }
                }
            }
        }
    }

    private <A, L> void addInitialStatesFromCS(TransitionSystem<Pair<List<L>, Map<String, Object>>,A, String> ts, Set<List<L>> initialLoc, Set<List<String>> initializations) {
        ParserBasedActDef ad = new ParserBasedActDef();
        for(List <L> initLoc: initialLoc){
            if(initializations.isEmpty()){
                addInitialStateFromCS(ts, initLoc, new HashMap<>());
            }
            else{
                Map<String, Object> eval = new HashMap<>();
                for(List<String> init : initializations){
                    for(String s : init){
                        eval = ad.effect(eval, s);
                    }
                    addInitialStateFromCS(ts, initLoc, eval);
                }
            }
        }
    }

    private <A, L> void addInitialStateFromCS(TransitionSystem<Pair<List<L>, Map<String, Object>>,A, String> ts, List<L> loc, Map<String, Object> eval) {
        Pair<List<L>, Map<String, Object>> newState = Pair.pair(loc, eval);
        ts.addState(newState);
        ts.setInitial(newState, true);
    }

    private <L, A> Set<List<String>> getInitializationsFromPgs(List<ProgramGraph<L,A>> pgs) {
        Set<List<String>> initializations = new HashSet<>();
        for(ProgramGraph<L,A> pg : pgs){
            if(initializations.isEmpty()){
                initializations.addAll(pg.getInitalizations());
            }
            else if(!pg.getInitalizations().isEmpty()){
                Set<List<String>> tempInitializations = new HashSet<>();
                for(List<String> init : initializations){
                    for(List<String> pgInit : pg.getInitalizations()){
                        List<String> temp = new ArrayList<>(init);
                        temp.addAll(pgInit);
                        tempInitializations.add(temp);
                    }
                }
                initializations = tempInitializations;
            }
        }
        return initializations;
    }

    private <L, A> Set<List<L>> getInitialLocFromPgs(List<ProgramGraph<L,A>> pgs) {
        Set<List<L>> initialLoc = new HashSet<>();
        for(ProgramGraph<L,A> pg : pgs){
            if(initialLoc.isEmpty()){
                initialLoc.add(new ArrayList<>(pg.getInitialLocations()));
            }
            else{
                Set<List<L>> tempInitialLoc = new HashSet<>();
                for(List<L> initLoc : initialLoc){
                    for(L loc : pg.getInitialLocations()){
                        List<L> temp = new ArrayList<>();
                        temp.addAll(initLoc);
                        temp.add(loc);
                        tempInitialLoc.add(temp);
                    }
                }
                initialLoc = tempInitialLoc;
            }
        }
        return initialLoc;
    }

    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        TransitionSystem<Pair<Sts, Saut>, A, Saut> result = createTransitionSystem();
        getInitialStatesOfProduct(ts,aut, result);
        addRestStates(ts,aut, result);
        return result;
    }

    private <Saut,A, P, Sts> void addRestStates(TransitionSystem<Sts,A,P> ts, Automaton<Saut,P> aut, TransitionSystem<Pair<Sts,Saut>,A,Saut> result) {
        List<Pair<Sts, Saut>> toCheck = new ArrayList<>(result.getInitialStates());
        List<Pair<Sts, Saut>> checked = new ArrayList<>();
        while (!toCheck.isEmpty()) {
            Pair<Sts, Saut> current = toCheck.get(0);
            checkState(current, checked, toCheck, ts,aut, result);
            checked.add(current);
            toCheck.remove(current);
        }
    }

    private <Saut, Sts, A, P> void checkState(Pair<Sts,Saut> current, List<Pair<Sts,Saut>> checked, List<Pair<Sts,Saut>> toCheck, TransitionSystem<Sts,A,P> ts, Automaton<Saut,P> aut, TransitionSystem<Pair<Sts,Saut>,A,Saut> result) {
        ts.getTransitions().forEach(trans -> {
            if (isStateFirstInTrans(current, trans)) {
                Set<Saut> next = aut.nextStates(current.getSecond(), ts.getLabel(trans.getTo()));
                if(next != null){
                    updateResultWithNextStates(current, checked, toCheck, ts, aut, result, trans);
                }
            }
        });
    }

    private <Saut, Sts, A, P> void updateResultWithNextStates(Pair<Sts, Saut> current, List<Pair<Sts, Saut>> checked, List<Pair<Sts, Saut>> toCheck, TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut, TransitionSystem<Pair<Sts, Saut>, A, Saut> result, Transition<Sts, A> trans) {
        Set<Saut> nextStates=aut.nextStates(current.getSecond(), ts.getLabel(trans.getTo()));
        Set<Pair<Sts, Saut>> newStates = new HashSet<>();
        nextStates.forEach(s->newStates.add(Pair.pair(trans.getTo(), s)));
        if (!newStates.isEmpty()) {
            addNewStatesToResult(current, checked, toCheck, result, trans, newStates);
        }
    }

    private <Saut, Sts, A> void addNewStatesToResult(Pair<Sts, Saut> current, List<Pair<Sts, Saut>> checked, List<Pair<Sts, Saut>> toCheck, TransitionSystem<Pair<Sts, Saut>, A, Saut> result, Transition<Sts, A> trans, Set<Pair<Sts, Saut>> newStates) {
        result.addAction(trans.getAction());
        newStates.forEach(s -> {
            addNewStateToResult(current, checked, toCheck, result, trans, s);
        });
    }

    private <Saut, Sts, A> void addNewStateToResult(Pair<Sts, Saut> current, List<Pair<Sts, Saut>> checked, List<Pair<Sts, Saut>> toCheck, TransitionSystem<Pair<Sts, Saut>, A, Saut> result, Transition<Sts, A> trans, Pair<Sts, Saut> s) {
        result.addAtomicProposition(s.getSecond());
        result.addState(s);
        result.addTransition(new Transition<>(current, trans.getAction(), s));
        result.addToLabel(s, s.getSecond());
        updateToCheck(checked, toCheck, s);
    }

    private <Saut, Sts> void updateToCheck(List<Pair<Sts, Saut>> checked, List<Pair<Sts, Saut>> toCheck, Pair<Sts, Saut> s) {
        if (!checked.contains(s)&& !toCheck.contains(s) ) {
            toCheck.add(s);
        }
    }

    private <Saut, Sts, A> boolean isStateFirstInTrans(Pair<Sts, Saut> state, Transition<Sts, A> trans) {
        return state.getFirst().equals(trans.getFrom());
    }

    private <Saut, Sts,A,P> void getInitialStatesOfProduct(TransitionSystem<Sts,A,P> ts, Automaton<Saut,P> aut, TransitionSystem<Pair<Sts, Saut>, A, Saut> result) {
        Set<Sts> tsInitials=ts.getInitialStates();
        Set<Saut> autInitials=aut.getInitialStates();
        tsInitials.forEach(tsInit->
                autInitials.forEach(autInit->{
                    Set<Pair<Sts,Saut>> initials = new HashSet<>();
                    Set<Saut> next = aut.nextStates(autInit, ts.getLabel(tsInit));
                    next.forEach(q->initials.add(Pair.pair(tsInit,q)));
                    for (Pair<Sts,Saut> init:
                            initials) {
                        result.addState(init);
                        result.setInitial(init, true);
                    }
                }));
    }


    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {

        NanoPromelaParser.StmtContext root_np= NanoPromelaFileReader.pareseNanoPromelaFile(filename);
        ProgramGraph<String, String> program_graph = new ProgramGraphImpl<>();
        String empty_string="";
        String root_txt=root_np.getText();
        programGraphFromNanoPromela_addLocation(program_graph,root_np);
        programGraphFromNanoPromelaHelp(root_np, root_txt, empty_string, empty_string, empty_string, program_graph);
        return program_graph;
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {

        NanoPromelaParser.StmtContext root_np=NanoPromelaFileReader.pareseNanoPromelaString(nanopromela);
        ProgramGraph<String, String> program_graph = new ProgramGraphImpl<>();
        String empty_string="";
        String root_txt=root_np.getText();
        programGraphFromNanoPromela_addLocation(program_graph,root_np);
        programGraphFromNanoPromelaHelp(root_np, root_txt, empty_string, empty_string, empty_string, program_graph);
        return program_graph;
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        NanoPromelaParser.StmtContext root_np=NanoPromelaFileReader.parseNanoPromelaStream(inputStream);
        ProgramGraph<String, String> program_graph = new ProgramGraphImpl<>();
        String empty_string="";
        String root_txt=root_np.getText();
        programGraphFromNanoPromela_addLocation(program_graph,root_np);
        programGraphFromNanoPromelaHelp(root_np, root_txt, empty_string, empty_string, empty_string, program_graph);
        return program_graph;
    }

    private void programGraphFromNanoPromela_addLocation(ProgramGraph<String, String> program_graph,
			StmtContext root_np) {
    	  String empty_string="";
    	  program_graph.addLocation(empty_string);
          String root_txt=root_np.getText();
          program_graph.addLocation(root_txt);
          program_graph.setInitial(root_txt, true);	
	}



	private void programGraphFromNanoPromelaHelp(ParseTree  root_np, String from_node, String post_np, String cond,
                                                 String to_node, ProgramGraph<String, String> program_graph) {

        int child_count;
        child_count=root_np.getChildCount();
        if (root_np instanceof NanoPromelaParser.IfstmtContext) {
            IfstmtContextHelp(root_np,from_node,post_np,cond,to_node,program_graph);
        }
        else if (root_np instanceof NanoPromelaParser.DostmtContext) {
            DostmtContextHelp(root_np,from_node,post_np,cond,to_node,program_graph);
        }
        else if (!(root_np instanceof NanoPromelaParser.DostmtContext))
            if(!(root_np instanceof NanoPromelaParser.IfstmtContext))
                if(!(root_np instanceof NanoPromelaParser.StmtContext)) {
                    OtherCase(root_np,from_node,post_np,cond,to_node,program_graph);
                }
                else if (child_count > 1) {
                    String child=root_np.getChild(1).getText();
                    String temp=";";
                    if(child.equals(temp)){
                        StmtContextHelp1(root_np,from_node,post_np,cond,to_node,program_graph);
                    }
                }
                else if (root_np instanceof NanoPromelaParser.StmtContext) {
                    StmtContextHelp2(root_np,from_node,post_np,cond,to_node,program_graph);
                }
    }

    private void OtherCase(ParseTree root_np, String from_node, String post_np, String cond, String to_node,
                                   ProgramGraph<String, String> program_graph) {

        String empty="";
        String temp="()";
        String to1=to_node;
        String to2= ";";
        String to3=post_np;
        String to_ans="";
        if (!(!(to1.equals(empty)) && !(to1.equals(temp))))
            to_ans=to3;
        else if (!(!(to3.equals(empty)) && !(to3.equals(temp))))
            to_ans=to1;
        else to_ans=to1+to2+to3;
        OtherCase_pgTransition(to_ans,root_np,from_node,cond,program_graph);
       
    }

    @SuppressWarnings("unchecked")
	private <L,A> void OtherCase_pgTransition(String to_ans, ParseTree root_np, String from_node, String cond,
			ProgramGraph<String, String> program_graph) {
		
   	 L to_np=(L) to_ans;
     A action_np=(A)root_np.getText();
     L from_np=(L) from_node;
     PGTransition<L, A> trans_pg = new PGTransition<>(from_np, cond, action_np, to_np);
     L loc_from=  trans_pg.getFrom();
     L loc_to=trans_pg.getTo();
     ((ProgramGraph<L, A>) program_graph).addLocation(loc_from);
     ((ProgramGraph<L, A>) program_graph).addLocation(loc_to);
     ((ProgramGraph<L, A>) program_graph).addTransition(trans_pg);
		
	}



	private void StmtContextHelp2(ParseTree root_np, String from_node, String post_np, String cond, String to_node,
                                  ProgramGraph<String, String> program_graph) {

        ParseTree child0=root_np.getChild(0);
        programGraphFromNanoPromelaHelp(child0, from_node, post_np, cond, to_node, program_graph);

    }

    private void StmtContextHelp1(ParseTree root_np, String from_node, String post_np, String cond, String to_node,
                                  ProgramGraph<String, String> program_graph) {
        String empty="";
        String temp="()";
        ParseTree child0=root_np.getChild(0);
        ParseTree child2=root_np.getChild(2);
        String post1=root_np.getChild(2).getText();
        String post2= ";";
        String post3=post_np;
        String post_ans="";
        if (!(!(post1.equals(empty)) && !(post1.equals(temp))))
            post_ans=post3;
        else if (!(!(post3.equals(empty)) && !(post3.equals(temp))))
            post_ans=post1;
        else post_ans=post1+post2+post3;
        programGraphFromNanoPromelaHelp(child0, from_node, post_ans, cond, to_node, program_graph);
        programGraphFromNanoPromelaHelp(child2, post_ans, post_np, empty, to_node, program_graph);
    }

    private  void DostmtContextHelp(ParseTree root_np, String from_node, String post_np, String cond, String to_node,
                                           ProgramGraph<String, String> program_graph) {

        String empty="";
        String temp="()";
        int i;
        int root_child_count=root_np.getChildCount() - 1;
        String neg = "";
        for (i = 1; i <root_child_count; i=i+1) {
            DostmtContextHelp_help( root_np,  from_node,  post_np,  cond,  to_node,    program_graph,i);
            String cond_ans = root_np.getChild(i).getChild(1).getText();
            String neg1=neg;
            String neg2="||";
            String neg3= "(" + cond_ans + ")";
            if (!(!(neg1.equals(empty)) && !(neg1.equals(temp))))
                neg=neg3;
            else if (!(!(neg3.equals(empty)) && !(neg3.equals(temp))))
                neg=neg1;
            else neg=neg1+neg2+neg3;
        }
        DostmtContextHelp_help2( root_np,  from_node,  post_np,  cond,  to_node,    program_graph,neg);
    }

    private  void DostmtContextHelp_help2(ParseTree root_np, String from_node, String post_np, String cond,
                                                 String to_node, ProgramGraph<String, String> program_graph, String neg) {
        String empty="";
        String temp="()";
        String fromTransAns="";
        String from_trans1=root_np.getText();
        String from_trans2= ";";
        String from_trans3= to_node + post_np;
        if (!(!(from_trans1.equals(empty)) && !(from_trans1.equals(temp))))
            fromTransAns=from_trans3;
        else if (!(!(from_trans3.equals(empty)) && !(from_trans3.equals(temp))))
            fromTransAns=from_trans1;
        else fromTransAns=from_trans1+from_trans2+from_trans3;
        String consitionTransAns="";
        String cond_trans1=cond;
        String cond_trans2= " && ";
        String cond_trans3= "(!(" + neg + "))";
        if (!(!(cond_trans1.equals(empty)) && !(cond_trans1.equals(temp))))
            consitionTransAns=cond_trans3;
        else if (!(!(cond_trans3.equals(empty)) && !(cond_trans3.equals(temp))))
            consitionTransAns=cond_trans1;
        else consitionTransAns=cond_trans1+cond_trans2+cond_trans3;
        
        DostmtContextHelp_help2_pgtransition(to_node,post_np,fromTransAns,program_graph,from_node,neg,consitionTransAns);
    }

    @SuppressWarnings("unchecked")
    private <L, A> void DostmtContextHelp_help2_pgtransition(String to_node, String post_np, String fromTransAns,
			ProgramGraph<String, String> program_graph, String from_node, String neg, String consitionTransAns) {
		
    	
    	String empty="";
 	   	L to_np=(L) (to_node + post_np);
        A action_np=(A) empty;
        L from_np=(L) fromTransAns;
        String cond_np="!(" + neg + ")";
        PGTransition<L, A> trans_pg = new PGTransition<>(from_np, cond_np, action_np, to_np);
        L loc_from=  trans_pg.getFrom();
        L loc_to=trans_pg.getTo();
        ((ProgramGraph<L, A>) program_graph).addLocation(loc_from);
        ((ProgramGraph<L, A>) program_graph).addLocation(loc_to);
        ((ProgramGraph<L, A>) program_graph).addTransition(trans_pg);
        L to1_np=(L) (to_node + post_np);
        A action1_np=(A) empty;
        L from1_np=(L) from_node;
        PGTransition<L, A> trans_pg1 = new PGTransition<>(from1_np, consitionTransAns, action1_np, to1_np);
        L loc_from1=  trans_pg1.getFrom();
        L loc_to1=trans_pg1.getTo();
        ((ProgramGraph<L, A>) program_graph).addLocation(loc_from1);
        ((ProgramGraph<L, A>) program_graph).addLocation(loc_to1);
        ((ProgramGraph<L, A>) program_graph).addTransition(trans_pg1);
		
	}




	private void DostmtContextHelp_help(ParseTree root_np, String from_node, String post_np, String cond,
                                        String to_node, ProgramGraph<String, String> program_graph, int i) {

    	DostmtContextHelp_help1( root_np,  from_node,  post_np,  cond,to_node,  program_graph,  i);
    	DostmtContextHelp_help2( root_np,  from_node,  post_np,  cond,to_node,  program_graph,  i);
                
    }
    	
    private void DostmtContextHelp_help2(ParseTree root_np, String from_node, String post_np, String cond,
			String to_node, ProgramGraph<String, String> program_graph, int i) {
	
    	 String empty="";
         String temp="()";
         String cond_ans = root_np.getChild(i).getChild(1).getText();
         ParseTree child= root_np.getChild(i).getChild(3);
        String from1=root_np.getText();
        String from2=";";
        String from3=to_node;
        String from_ans="";
        if (!(!(from1.equals(empty)) && !(from1.equals(temp))))
            from_ans=from3;
        else if (!(!(from3.equals(empty)) && !(from3.equals(temp))))
            from_ans=from1;
        else from_ans=from1+from2+from3;
        String from1_new=from_ans;
        String from2_new=";";
        String from3_new=post_np;
        String from_ans_new="";
        if (!(!(from1_new.equals(empty)) && !(from1_new.equals(temp))))
            from_ans_new=from3_new;
        else if (!(!(from3_new.equals(empty)) && !(from3_new.equals(temp))))
            from_ans_new=from1_new;
        else from_ans_new=from1_new+from2_new+from3_new;
        String post1=root_np.getText();
        String post2= ";";
        String post3=post_np;
        String post_ans="";
        if (!(!(post1.equals(empty)) && !(post1.equals(temp))))
            post_ans=post3;
        else if (!(!(post3.equals(empty)) && !(post3.equals(temp))))
            post_ans=post1;
        else post_ans=post1+post2+post3;
        String cond3="(" + cond_ans + ")";
        programGraphFromNanoPromelaHelp(child,from_ans_new, post_ans, cond3, to_node, program_graph);
    
		
	}

	private void DostmtContextHelp_help1(ParseTree root_np, String from_node, String post_np, String cond,
			String to_node, ProgramGraph<String, String> program_graph, int i) {
	
    	  String empty="";
          String temp="()";
          String cond_ans = root_np.getChild(i).getChild(1).getText();
          ParseTree child= root_np.getChild(i).getChild(3);
          String post1=root_np.getText();
          String post2= ";";
          String post3=post_np;
          String post_ans="";
          if (!(!(post1.equals(empty)) && !(post1.equals(temp))))
              post_ans=post3;
          else if (!(!(post3.equals(empty)) && !(post3.equals(temp))))
              post_ans=post1;
          else post_ans=post1+post2+post3;
          String cond1="(" + cond + ")";
          String cond2=" && ";
          String cond3="(" + cond_ans + ")";
          String cond_ans_update="";
          if (!(!(cond1.equals(empty)) && !(cond1.equals(temp))))
              cond_ans_update=cond3;
          else if (!(!(cond3.equals(empty)) && !(cond3.equals(temp))))
              cond_ans_update=cond1;
          else cond_ans_update=cond1+cond2+cond3;
          programGraphFromNanoPromelaHelp(child, from_node, post_ans,cond_ans_update, to_node, program_graph);
	}

	private void IfstmtContextHelp(ParseTree root_np, String from_node, String post_np, String cond, String to_node,
                                   ProgramGraph<String, String> program_graph) {

        String empty="";
        String temp="()";
        int i;
        int root_child_count=root_np.getChildCount() - 1;
        for ( i = 1; i < root_child_count; i=i+1) {
            ParseTree child= root_np.getChild(i).getChild(3);
            String cond1="(" + cond + ")";
            String cond2=" && ";
            String cond3="(" + root_np.getChild(i).getChild(1).getText() + ")";
            String cond_ans="";
            if (!(!(cond1.equals(empty)) && !(cond1.equals(temp))))
                cond_ans=cond3;
            else if (!(!(cond3.equals(empty)) && !(cond3.equals(temp))))
                cond_ans=cond1;
            else cond_ans=cond1+cond2+cond3;
            programGraphFromNanoPromelaHelp(child, from_node, post_np,cond_ans, to_node, program_graph);
        }
    }

    @Override
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts, Automaton<Saut, P> aut) {
        TransitionSystem<Pair<S, Saut>, A, Saut> product = product(ts,aut);
        Set<Saut> accStates = aut.getAcceptingStates();
        Set<Pair<S, Saut>> initialStates=product.getInitialStates();
        for(Pair<S, Saut> s0 : initialStates){
            List<Pair<S, Saut>> DFSresult = DFS(s0, product, accStates);
            for(Pair<S, Saut> s : DFSresult){
                VerificationResult<S> failed = checkForCycle(product, accStates, s0, s);
                if (failed != null)
                    return failed;
            }
        }
        return new VerificationSucceeded<>();
    }

    private <S, A, Saut> VerificationResult<S> checkForCycle(TransitionSystem<Pair<S, Saut>, A, Saut> product, Set<Saut> accStates, Pair<S, Saut> s0, Pair<S, Saut> s) {
        if(!DFS(s, product, accStates).contains(s))
            return null;
        return createFailedFromCycle(product, s0, s);
    }

    private <S, A, Saut> VerificationFailed<S> createFailedFromCycle(TransitionSystem<Pair<S, Saut>, A, Saut> product, Pair<S, Saut> s0, Pair<S, Saut> s) {
        VerificationFailed<S> failed = new VerificationFailed<>();
        List<S> circle = path(s, s, product);
        circle.remove(0);
        failed.setCycle(circle);
        failed.setPrefix(path(s0, s, product));
        return failed;
    }

    private <S, A, P, Saut> List<Pair<S,Saut>> DFS(Pair<S,Saut> start, TransitionSystem<Pair<S,Saut>, A, P> ts, Set<Saut> badStates){
        ArrayList<Pair<S,Saut>> toCheck = new ArrayList<>(ts.getStates());
        Stack<Pair<S,Saut>> stack = new Stack<>();
        List<Pair<S,Saut>> result = new ArrayList<>();
        stack.push(start);
        while(!stack.isEmpty()){
            DFSstep(ts, badStates, result, toCheck, stack);
        }
        return result;
    }

    private <S, A, P, Saut> void DFSstep(TransitionSystem<Pair<S, Saut>, A, P> ts, Set<Saut> badStates, List<Pair<S, Saut>> result, ArrayList<Pair<S, Saut>> toCheck, Stack<Pair<S, Saut>> stack) {
        Pair<S,Saut> state = stack.pop();
        Set<Transition<Pair<S, Saut>, A>> transitionsWithState = createTransitionsWithStateAsGetFrom(ts, state);
        transitionsWithState.forEach(transition->{
            updateStack(toCheck, stack, transition);
            updateResult(badStates, result, transition);
        });
        toCheck.remove(state);
    }

    private <S, A, P, Saut> Set<Transition<Pair<S, Saut>, A>> createTransitionsWithStateAsGetFrom(TransitionSystem<Pair<S, Saut>, A, P> ts, Pair<S, Saut> state) {
        Set<Transition<Pair<S, Saut>, A>> transitions=ts.getTransitions();
        Set<Transition<Pair<S, Saut>, A>> transitionsWithState=new HashSet<>();
        transitions.forEach(transition->{
            if(state.equals(transition.getFrom()))
                transitionsWithState.add(transition);
        });
        return transitionsWithState;
    }

    private <S, A, Saut> void updateResult(Set<Saut> badStates, List<Pair<S, Saut>> result, Transition<Pair<S, Saut>, A> transition) {
        if(!result.contains(transition.getTo()) && badStates.contains(transition.getTo().getSecond()) ) {
            result.add(transition.getTo());
        }
    }

    private <S, A, Saut> void updateStack(ArrayList<Pair<S, Saut>> toCheck, Stack<Pair<S, Saut>> stack, Transition<Pair<S, Saut>, A> transition) {
        if(!stack.contains(transition.getTo())&&toCheck.contains(transition.getTo()) ) {
            stack.push(transition.getTo());
        }
    }

    private <S, A, P, Saut> List<S> path(Pair<S,Saut> start, Pair<S,Saut> end, TransitionSystem<Pair<S,Saut>, A, P> ts){
        Map<Pair<S,Saut>,List<List<S>>> paths = new HashMap<>();
        paths.put(start, Collections.singletonList(Collections.singletonList(start.getFirst())));
        Stack<Pair<S,Saut>> stack = new Stack<>();
        stack.push(start);
        ArrayList<Pair<S,Saut>> toCheck = new ArrayList<>(ts.getStates());
        while(!stack.isEmpty()){
            innerDFSstep(ts, toCheck, paths, stack);
        }
        return paths.get(end).get(0);
    }

    private <S, A, P, Saut> void innerDFSstep(TransitionSystem<Pair<S, Saut>, A, P> ts, ArrayList<Pair<S, Saut>> toCheck, Map<Pair<S, Saut>, List<List<S>>> paths, Stack<Pair<S, Saut>> stack) {
        Pair<S,Saut> state = stack.pop();
        toCheck.remove(state);
        Set<Transition<Pair<S, Saut>, A>> transitionsWithState = createTransitionsWithStateAsGetFrom(ts, state);
        transitionsWithState.forEach(transition->{
            updateStack(toCheck, stack, transition);
            updatePath(paths, transition);
        });
    }

    private <S, A, Saut> void updatePath(Map<Pair<S, Saut>, List<List<S>>> paths, Transition<Pair<S, Saut>, A> transition) {
        List<List<S>> toAdd = new ArrayList<>();
        Pair<S, Saut> state=transition.getFrom();
        paths.get(state).forEach(lst ->{
            List<S> tmpList = new ArrayList<>(lst);
            tmpList.add(transition.getTo().first);
            toAdd.add(tmpList);
        });
        paths.put(transition.getTo(), toAdd);
    }

    @Override
    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement LTL2NBA
    }

    @Override
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement GNBA2NBA
    }
    
    private <S, A, P> void check_state_exist(TransitionSystem<S, A, P> ts,S state) {
        if(!ts.getStates().contains(state))
            throw new StateNotFoundException(state);

    }
    private <S, A, P> void check_action_exist(TransitionSystem<S, A, P> ts, A action) {
        if(!ts.getActions().contains(action))
            throw new ActionNotFoundException(action);
    }

   
}
