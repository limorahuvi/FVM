package il.ac.bgu.cs.fvm.impl;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import il.ac.bgu.cs.fvm.exceptions.*;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;

public class TransitionSystemImp<STATE,ACTION,ATOMIC_PROPOSITION>
        implements TransitionSystem<STATE,ACTION,ATOMIC_PROPOSITION>{

    private String name;
    private Set<STATE> initialStates;
    private Set<STATE> states;
    private Set<ACTION> actions;
    private Set<Transition<STATE,ACTION>> transitions;
    private Set<ATOMIC_PROPOSITION> atomicPropositions;
    private Map<STATE, Set<ATOMIC_PROPOSITION>> labelingFunctions;

    public TransitionSystemImp() {
        this.name = "";
        initSets();
    }

    private void initSets(){
        this.initialStates = new HashSet<STATE>();
        this.states = new HashSet<STATE>(); ;
        this.actions = new HashSet<ACTION>();
        this.transitions = new HashSet<Transition<STATE,ACTION>>();
        this.atomicPropositions = new HashSet<ATOMIC_PROPOSITION>();
        this.labelingFunctions = new HashMap<STATE, Set<ATOMIC_PROPOSITION>>();
    }

    @Override
    public String getName() {
        return this.name;
    }

    @Override
    public void setName(String name) {
        this.name=name;
    }

    @Override
    public void addAction(ACTION anAction) {
        this.actions.add(anAction);
    }

    @Override
    public void setInitial(STATE aState, boolean isInitial) throws StateNotFoundException {
        if(!checkIfStateExist(aState))
            throw new StateNotFoundException(aState);
        if(isInitial){
            initialStates.add(aState);
        }
        else if(this.initialStates.contains(aState)){
            initialStates.remove(aState);
        }
    }

    @Override
    public void addState(STATE state) {
        this.labelingFunctions.put(state, new HashSet<ATOMIC_PROPOSITION>());
        this.states.add(state);
    }

    @Override
    public void addTransition(Transition<STATE, ACTION> t) throws FVMException {
        if(checkIfStateOrActionExist(t))
        {
            this.transitions.add((t));
        }
        else{
            throw new InvalidTransitionException(t);
        }
    }


    @Override
    public Set<ACTION> getActions() {
        Set<ACTION> actionsCopy = new HashSet<ACTION>();
        actionsCopy.addAll(this.actions);
        return actionsCopy;
    }

    @Override
    public void addAtomicProposition(ATOMIC_PROPOSITION p) {
        if(!this.atomicPropositions.contains(p))
            this.atomicPropositions.add(p);

    }

    @Override
    public Set<ATOMIC_PROPOSITION> getAtomicPropositions() {
        return this.atomicPropositions;
    }

    @Override
    public void addToLabel(STATE s, ATOMIC_PROPOSITION l) throws FVMException {
        if(!checkIfStateExist(s))
            throw new StateNotFoundException(s);
        if(!checkIfAtomicPrositionExist(l))
            throw new FVMException("Atomic Proposition doesn't exist");
        if(!this.labelingFunctions.get(s).contains(l))
            this.labelingFunctions.get(s).add(l);

    }

    @Override
    public Set<ATOMIC_PROPOSITION> getLabel(STATE s) {
        if(!this.checkIfStateExist(s)){
            throw new StateNotFoundException(s);
        }
        if(this.labelingFunctions.containsKey(s))
            return this.labelingFunctions.get(s);
        return new HashSet<ATOMIC_PROPOSITION>();
    }

    @Override
    public Set<STATE> getInitialStates() {
        return this.initialStates;
    }

    @Override
    public Map<STATE, Set<ATOMIC_PROPOSITION>> getLabelingFunction() {
        return this.labelingFunctions;
    }

    @Override
    public Set<STATE> getStates() {
        return this.states;
    }

    @Override
    public Set<Transition<STATE,ACTION>> getTransitions() {
        return this.transitions;
    }

    @Override
    public void removeAction(ACTION action) throws FVMException {
        for(Transition<STATE,ACTION> t : this.transitions) {
            if(t.getAction().equals(action))
                throw new DeletionOfAttachedActionException(t.getFrom(), TransitionSystemPart.ACTIONS);
        }
        this.actions.remove(action);

    }

    @Override
    public void removeAtomicProposition(ATOMIC_PROPOSITION p) throws FVMException {
        for(Map.Entry<STATE, Set<ATOMIC_PROPOSITION>> entry: this.labelingFunctions.entrySet()) {
            if(entry.getValue().contains(p))
                throw new DeletionOfAttachedAtomicPropositionException(entry.getKey(), TransitionSystemPart.ATOMIC_PROPOSITIONS);
        }
        this.atomicPropositions.remove(p);

    }

    @Override
    public void removeLabel(STATE s, ATOMIC_PROPOSITION l) {
        this.labelingFunctions.get(s).remove(l);
    }

    @Override
    public void removeState(STATE state) throws FVMException {
        if(stateIsInUseByATransition(state)!=null)
            throw new DeletionOfAttachedStateException(state, TransitionSystemPart.TRANSITIONS);
        if(stateIsLabled(state))
            throw new DeletionOfAttachedStateException(state, TransitionSystemPart.LABELING_FUNCTION);
        if(isInTheSetOfInitialStates(state)) {
            throw new DeletionOfAttachedStateException(state, TransitionSystemPart.INITIAL_STATES);
        }
        this.states.remove(state);

    }

    @Override
    public void removeTransition(Transition<STATE, ACTION> t) {
        this.transitions.remove(t);

    }

    private boolean isInTheSetOfInitialStates(STATE state) {
        return this.initialStates.contains(state);
    }

    private boolean stateIsLabled(STATE state) {
        if(!this.labelingFunctions.containsKey(state))
            return false;
        if(this.labelingFunctions.get(state).isEmpty())
            return false;
        return true;
    }

    private boolean checkIfAtomicPrositionExist(ATOMIC_PROPOSITION l) {
        return this.atomicPropositions.contains(l);
    }

    private boolean checkIfStateExist(STATE s) {
        return this.states.contains(s);
    }

    private Transition stateIsInUseByATransition(STATE state) {
        for(Transition<STATE,ACTION> t : this.transitions) {
            if(t.getFrom().equals(state) || t.getTo().equals(state))
                return t;
        }
        return null;
    }

    private boolean checkIfStateOrActionExist(Transition<STATE, ACTION> t) {
        if(this.states.contains(t.getFrom()) && this.states.contains(t.getTo()) && this.actions.contains(t.getAction())){
            return true;
        }
        return false;
    }


}
