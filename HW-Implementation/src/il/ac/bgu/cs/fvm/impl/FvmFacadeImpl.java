package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import java.io.InputStream;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

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
            for (A action :actions) {
                for (S state :states) {
                    Set<S> post_set=post(ts, state, action);
                    int size_post=post_set.size();
                    if (size_post > 1) {
                       return false;
                   }
               }
           }
        }
        else
            return false;
        return true;
    }

    
    @Override
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {

    	Set<S> init_set=ts.getInitialStates();
		int size_set_init=init_set.size();
		if(size_set_init<=1){

        int same=0;
        Set<S> states=ts.getStates();
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
		}
		else
			return false;
        return true;
    }
    
    private <S, A, P> boolean isAPDeterministicHelp(TransitionSystem<S, A, P> ts, Set<P> labels, S s_post){
        if(ts.getLabel(s_post).containsAll(labels) && labels.containsAll(ts.getLabel(s_post))) {
            return true;
        }
        return false;
    }
    

    @Override
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if(isInitialExecutionFragment(ts, e) && isMaximalExecutionFragment(ts, e)){
            return true;
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
        check_state_exist(ts,temp.head());
        return true;

    }

    private <S, A, P> boolean isLegalTransition(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> temp) {
        A action=temp.tail().head();
        S from = temp.head();
        S to=temp.tail().tail().head();
        Set<Transition<S, A>> transitions=ts.getTransitions();
        for(Transition<S, A> transition : transitions) {
            if(transition.getFrom().equals(from) && transition.getAction().equals(action)
                    && transition.getTo().equals(to))
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
            if(fromS.equals(s)){
                S Tos=transition.getTo();
                post_set.add(Tos);
            }
        }
        return post_set;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        for(S state: c) {
            check_state_exist(ts, state);
        }
        Set<S> post_set = new HashSet<S>();
        for(Transition<S, ?> transition : ts.getTransitions()) {
            S fromS=transition.getFrom();
            if(c.contains(fromS))
            {
                S Tos=transition.getTo();
                post_set.add(Tos);
            }
        }
        return post_set;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
        check_action_exist(ts,a);
        check_state_exist(ts, s);
        Set<S> post_set = new HashSet<S>();
        for(Transition<S, A> transition : ts.getTransitions() ) {
            S fromS=transition.getFrom();
            if(fromS.equals(s) && transition.getAction().equals(a))
            {
                S Tos=transition.getTo();
                post_set.add(Tos);
            }
        }
        return post_set;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        check_action_exist(ts,a);
        Set<S> states =ts.getStates();
        for(S state :states) {
            check_state_exist(ts, state);
        }
        Set<S> post_set = new HashSet<S>();
        for(Transition<S, A> transition : ts.getTransitions()) {
            S fromS=transition.getFrom();
            if(c.contains(fromS) && transition.getAction().equals(a))
            {
                S Tos=transition.getTo();
                post_set.add(Tos);
            }
        }
        return post_set;
    }
    
    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        check_state_exist(ts, s);
        Set<S> pre_set=new HashSet<S>();
        for(Transition<S, ?> transition : ts.getTransitions()) {
            S Tos=transition.getTo();
            if(Tos.equals(s)){
                S fromS=transition.getFrom();
                pre_set.add(fromS);
            }
        }
        return pre_set;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        for(S state: c) {
            check_state_exist(ts, state);
        }
        Set<S> pre_set = new HashSet<S>();
        for(Transition<S, ?> transition : ts.getTransitions()) {
            S Tos=transition.getTo();
            if(c.contains(Tos))
            {
                S fromS=transition.getFrom();
                pre_set.add(fromS);
            }
        }
        return pre_set;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {

        check_action_exist(ts,a);
        check_state_exist(ts, s);
        Set<S> pre_set = new HashSet<S>();
        for(Transition<S, A> transition : ts.getTransitions() ) {
            S ToS=transition.getTo();
            if(ToS.equals(s) && transition.getAction().equals(a))
            {
                S fromS=transition.getFrom();
                pre_set.add(fromS);
            }
        }
        return pre_set;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        check_action_exist(ts,a);
        Set<S> states =ts.getStates();
        for(S state :states) {
            check_state_exist(ts, state);
        }
        Set<S> pre_set = new HashSet<S>();
        for(Transition<S, A> transition : ts.getTransitions()) {
            S Tos=transition.getTo();
            if(c.contains(Tos) && transition.getAction().equals(a))
            {
                S fromS=transition.getFrom();
                pre_set.add(fromS);
            }
        }
        return pre_set;
    }

    @Override
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {

        Set<S> reach_states = new HashSet<S>();
        reach_help(reach_states,ts);
        boolean found = true;
        boolean isAdded = false;
        while(found ==true) {
            found = false;
            for(Transition<S, A> transition : ts.getTransitions()) {
                isAdded = false;
                S fromS=transition.getFrom();
                if(reach_states.contains(fromS)) {
                    S getS=transition.getTo();
                    isAdded = reach_states.add(getS);
                    if(isAdded)
                        found = true;
                }
            }
        }
        return reach_states;
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

    private <T> List<T> unionToList (Set<T> s1, Set<T> s2){
        List<T> unioned = Stream.concat(s1.stream(), s2.stream()).collect(Collectors.toList());
        return unioned;
    }

    private <T> Set<T> intersection (Set<T> s1, Set<T> s2){
        Set<T> intersectioned = new HashSet<>();
        for(T a:s1){
            for(T b:s2){
                if(a.equals(b)){
                    intersectioned.add(a);
                }
            }
        }
        return intersectioned;
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
//        private Set<PGTransition<L, A>> p_transitions;

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
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromCircuit
    }

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromProgramGraph
    }

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromChannelSystem
    }

    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement product
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromelaString
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    //=============================================================================
    //=============================================================================

    @Override
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement verifyAnOmegaRegularProperty
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
