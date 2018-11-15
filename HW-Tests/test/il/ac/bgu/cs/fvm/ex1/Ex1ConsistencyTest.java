package il.ac.bgu.cs.fvm.ex1;

import static il.ac.bgu.cs.fvm.TSTestUtils.makeLinearTs;
import static org.junit.Assert.fail;

import org.junit.Before;
import org.junit.Test;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.exceptions.FVMException;
import il.ac.bgu.cs.fvm.exceptions.InvalidLablingPairException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;

/**
 * Testing the consistency of a transition system implementation.
 * @author michael
 */
//V
public class Ex1ConsistencyTest {
    
    FvmFacade sut = null;
    
    @Before
    public void setup() {
        sut = FvmFacade.createInstance();
    }
    
    @Test(expected=FVMException.class, timeout=2000)
    public void transitionToNonexistentState() {
        TransitionSystem<Integer, String, String> ts = makeLinearTs(5);
        ts.addTransition( new Transition<>(1, "a2", 700) );
        fail("Accepted illegal transition: Destination state 700 does not exist.");
    }

    @Test(expected=FVMException.class, timeout=2000)
    public void transitionFromNonexistentState() {
        TransitionSystem<Integer, String, String> ts = makeLinearTs(5);
        ts.addTransition( new Transition<>(700, "a2", 1));
        fail("Accepted illegal transition: Source state 700 does not exist.");
    }
    
    @Test(expected=FVMException.class, timeout=2000)
    public void transitionWithNonexistentAction() {
        TransitionSystem<Integer, String, String> ts = makeLinearTs(5);
        ts.addTransition( new Transition<>(1, "not-an-action", 2));
        fail("Accepted illegal transition: Action 'not-an-action' does not exist.");
    }
    
    @Test(expected=StateNotFoundException.class, timeout=2000)
    public void illegalInitialState() {
        TransitionSystem<Integer, String, String> ts = makeLinearTs(5);
        ts.setInitial( 700, true );
        fail("Accepted an illegal initial state");
    }
    
    @Test(expected=InvalidLablingPairException.class, timeout=2000)
    public void illegalLabel() {
        TransitionSystem<Integer, String, String> ts = makeLinearTs(4);
        ts.addAtomicProposition("g");
        ts.addToLabel( 1, "not-there" );
        fail("Accepted an illegal label");
    }
    
    @Test(expected=StateNotFoundException.class, timeout=2000)
    public void preForNonexistentState() {
        TransitionSystem<Integer, String, String> ts = makeLinearTs(4);
        sut.pre(ts, 404);
        fail("Did not throw an exception while calculating pre for a nonexistent state");
    }
    
    @Test(expected=StateNotFoundException.class, timeout=2000)
    public void postForNonexistentState() {
        TransitionSystem<Integer, String, String> ts = makeLinearTs(4);
        sut.post(ts, 404);
        fail("Did not throw an exception while calculating post for a nonexistent state");
    }            
}
