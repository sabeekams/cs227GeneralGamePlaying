package player.gamer.statemachine.cs227b;

import java.util.ArrayList;
import java.util.List;

import util.statemachine.exceptions.MoveDefinitionException;
import util.statemachine.exceptions.TransitionDefinitionException;
import util.statemachine.implementation.prover.ProverStateMachine;
import util.statemachine.MachineState;
import util.statemachine.Move;
import util.statemachine.Role;

public class CachingProverStateMachine extends ProverStateMachine
{
	// The List key must be a tuple of MachineState, Role
	private StateMachineCache<List<Object>, List<Move>> movesCache;
	// The List key must be a tuple of MachineState, List<Move>
	private StateMachineCache<List<Object>, MachineState> nextStatesCache;
	// Cache terminal states as true and non-terminal states as false;	
	private StateMachineCache<MachineState, Boolean> terminalStatesCache;

	public CachingProverStateMachine() {
		movesCache = new StateMachineCache<List<Object>, List<Move>>();
		nextStatesCache = new StateMachineCache<List<Object>, MachineState>();
		terminalStatesCache = new StateMachineCache<MachineState, Boolean>();
	}
	
	@Override
	public List<Move> getLegalMoves(MachineState state, Role role) throws MoveDefinitionException
	{
		ArrayList<Object> key = new ArrayList<Object>();
		key.add(state); key.add(role);
		
		List<Move> moves  = movesCache.retrieve(key);
		if (moves == null) {
			moves = super.getLegalMoves(state, role);
			movesCache.cache(key, moves);
		}
		return moves;
	}
	
	@Override
	public MachineState getNextState(MachineState state, List<Move> moves) throws TransitionDefinitionException
	{
		ArrayList<Object> key = new ArrayList<Object>();
		key.add(state); key.add(moves);
		
		MachineState nextState  = nextStatesCache.retrieve(key);
		if (nextState == null) {
			nextState = super.getNextState(state, moves);
			nextStatesCache.cache(key, nextState);
		}
		return nextState;
	}
	
	//@Override
	public boolean isTerminal(MachineState state)
	{
		Boolean boolValue = terminalStatesCache.retrieve(state);
		
		if (boolValue == null) {
			boolValue = super.isTerminal(state);
			terminalStatesCache.cache(state, boolValue);
		}
		return boolValue;
	}
	
	public void report() {
		System.out.println("Next states cache:");
		nextStatesCache.report();
		System.out.println("Terminal states cache:");
		//terminalStatesCache.report();
		System.out.println("Moves cache cache:");
		movesCache.report();

	}

	public void SwapCachesIfNeeded() {
		if (!SystemCalls.isMemoryAvailable()) {
			movesCache.swapCaches();
			nextStatesCache.swapCaches();
			//terminalStatesCache.swapCaches();
		}
	}
	
	@Override
	public void doPerMoveWork() {
		SwapCachesIfNeeded();
		super.doPerMoveWork();
	}
}