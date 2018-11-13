package il.ac.bgu.cs.fvm.impl;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import il.ac.bgu.cs.fvm.exceptions.FVMException;
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

public class ProgramGraphImpl<L, A> implements ProgramGraph<L, A> {

    private String name;
    private Set<L> locations_init;
    private Set<L> locations;
    private Set<List<String>> initialstates;
    private Set<PGTransition<L, A>> p_transitions;

    ProgramGraphImpl(){
        name = "Program Graph";
        locations_init = new HashSet<>();
        locations = new HashSet<>();
        initialstates = new HashSet<>();
        p_transitions = new HashSet<>();
    }
        
        @Override
	public void addInitalization(List<String> init) {
        	initialstates.add(init);
	}

	@Override
	public void setInitial(L location, boolean isInitial) {
		if(locations.contains(location)){
			locations_init.add(location);
		}
		else{
			throw new FVMException("invalid init state");
		}	
	}

	@Override
	public void addLocation(L l) {
		locations.add(l);
	}

	@Override
	public void addTransition(PGTransition<L, A> t) {
			L from=t.getFrom();
			L to =t.getTo();
			if(locations.contains(from)){
				if(locations.contains(to)){
					p_transitions.add(t);
				}
				 throw new FVMException("Invalid transition");
			}
			 throw new FVMException("Invalid transition");
	}

	@Override
	public Set<List<String>> getInitalizations() {
		return initialstates;
	}

	@Override
	public Set<L> getInitialLocations() {
		return locations_init;
	}

	@Override
	public Set<L> getLocations() {
		return locations;
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public Set<PGTransition<L, A>> getTransitions() {
		return p_transitions;
	}

	@Override
	public void removeLocation(L l) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void removeTransition(PGTransition<L, A> t) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setName(String name) {
		// TODO Auto-generated method stub
		
	}

}
