package player.gamer.statemachine.cs227b;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Random;
import java.util.Set;

import util.gdl.grammar.GdlFunction;
import util.gdl.grammar.GdlSentence;
import util.propnet.architecture.components.Proposition;
import util.statemachine.MachineState;
import util.statemachine.Role;
import util.statemachine.exceptions.GoalDefinitionException;
import util.statemachine.exceptions.MoveDefinitionException;
import util.statemachine.exceptions.TransitionDefinitionException;
import util.statemachine.Move;

public class FasterPropNetStateMachine extends PruningPropNetStateMachine {

	private HashMap<Integer, Proposition> mapIntToBaseProps;
	private HashMap<Proposition, Integer> mapBasePropsToInt;

	public void additionalInit() {
		mapBasePropositions();
	}

	//Creates map of integer keys to base props, and a reverse map of base props to those "keys"
	public void mapBasePropositions(){
		mapIntToBaseProps = new HashMap<Integer, Proposition>();
		mapBasePropsToInt = new HashMap<Proposition, Integer>();
		int key=0;

		for (Proposition p: propNet.getBasePropositions().values()) {
			mapIntToBaseProps.put(key, p);
			mapBasePropsToInt.put(p, key);
			key++;
		}
	}

	public OurMachineState convertMachineState(MachineState state){
		OurMachineState ourMS = new OurMachineState();
		Set<GdlSentence> contents = state.getContents();

		for (Proposition p : propNet.getBasePropositions().values()){
			if (contents.contains(p.getName().toSentence())){
				ourMS.add(mapBasePropsToInt.get(p)); 
			}
		}
		return ourMS;
	}

	public int getOutPrunedScore(OurMachineState state, Role role) {
		SetOurBasePropositions(state);
		for (Proposition p: trueLatchesToRequiringGoals.keySet()) {
			if (p.getValue() && trueLatchesToRequiringGoals.get(p).get(role) != null) {
				return extractGoalNodeScore(trueLatchesToRequiringGoals.get(p).get(role));
			}
		}
		int uninhibited = propNet.getGoalPropositions().get(role).size();
		Proposition lastUninhibited = null;
		for (Proposition p: trueLatchesToInhibitedGoals.keySet()) {
			if (trueLatchesToInhibitedGoals.get(p).get(role) != null) {
				if (p.getValue()) {
					uninhibited--;
				} else {
					lastUninhibited = p;
				}
			}
			if (p.getValue() && trueLatchesToInhibitedGoals.get(p).get(role) != null) {
				return extractGoalNodeScore(trueLatchesToInhibitedGoals.get(p).get(role));
			}
		}
		if (uninhibited == 1) {
			System.out.println("THIS ALSO SHOULDN'T BE");
			return extractGoalNodeScore(lastUninhibited);
		}
		System.out.println("ERROR WITH PRUNED SCORE");
		return 0;
	}

	public boolean pruneOurState(OurMachineState state, Role role) {
		if (trueLatchesToRequiringGoals.size() >= 1 || falseLatchesToRequiringGoals.size() >= 1) {
			SetOurBasePropositions(state);
			for (Proposition p: trueLatchesToRequiringGoals.keySet()) {
				if (p.getValue() && trueLatchesToRequiringGoals.get(p).get(role) != null) {
					return true;
				}
			}
			int uninhibited = propNet.getGoalPropositions().get(role).size();
			for (Proposition p: trueLatchesToInhibitedGoals.keySet()) {
				if (p.getValue() && trueLatchesToInhibitedGoals.get(p).get(role) != null) {
					uninhibited--;
				}
			}
			if (uninhibited == 1) {
				System.out.println("THIS SHOULDN'T BE");
				return true;
			}
		}
		return false;
	}

	public int getOurGoal(OurMachineState state, Role theRole)
			throws GoalDefinitionException {
		SetOurBasePropositions(state);
		Propagate(goalOrderings.get(theRole));
		for (Proposition goal: propNet.getGoalPropositions().get(theRole)) {
			if (goal.getValue()) return extractGoalNodeScore(goal);
		}
		System.out.println("ERROR GETTING GOAL");
		return 0;
	}

	public boolean isOurTerminal(OurMachineState state) {
		//		Timer t = new Timer();
		SetOurBasePropositions(state);
		Propagate(terminalOrdering);
		//		t.stop();
		//		Timer.report();
		return propNet.getTerminalProposition().getValue();
	}


	public OurMachineState getOurInitialState() {
		OurMachineState result = new OurMachineState();
		propNet.getInitProposition().setValue(true);
		for (Proposition p: propNet.getBasePropositions().values()) {
			if (p.getSingleInput().getValue()) {
				result.add(mapBasePropsToInt.get(p));
			}
			p.setValue(p.getSingleInput().getValue());
		}
		return result;
	}

	public List<Move> getOurLegalMoves(OurMachineState state, Role role)
			throws MoveDefinitionException {
		List<GdlSentence> moves = new ArrayList<GdlSentence>();
		SetOurBasePropositions(state);
		Propagate(legalOrderings.get(role));
		for (Proposition p: propNet.getLegalPropositions().get(role)) {
			if (p.getValue()) {
				GdlFunction func = (GdlFunction)p.getName();
				moves.add(func.getBody().get(1).toSentence());
			}
		}
		return Move.gdlToMoves(moves);
	}


	public OurMachineState getOurNextState(OurMachineState state, List<Move> moves)
			throws TransitionDefinitionException {
		SetOurBasePropositions(state);
		SetInputPropositions(moves);
		Propagate(nextStateOrdering);

		OurMachineState nextState = new OurMachineState();
		for (Proposition p: propNet.getBasePropositions().values()) {
			if (p.getSingleInput().getValue()) {
				nextState.add(mapBasePropsToInt.get(p));
			}
		}
		return nextState;
	}
	
	private void SetOurBasePropositions(OurMachineState state) {
		propNet.getInitProposition().setValue(false);

		Set<Integer> contents = state.getContents();

		for (Proposition p: propNet.getBasePropositions().values()) {
			p.setValue(false);
		}
		for (Integer i : contents) {
			Proposition p = mapIntToBaseProps.get(i);
			p.setValue(true);
		}
	}

	public OurMachineState performOurDepthCharge(OurMachineState state, Role role, int[] theDepth, int[] theScore, long finishBy) throws TransitionDefinitionException, MoveDefinitionException {  
		int nDepth = 0;
		while(true) {
			if (isOurTerminal(state)) {
				try {
					theScore[0] = getOurGoal(state, role);
				} catch (GoalDefinitionException e) {
					e.printStackTrace();
				}
				break;
			} else if (pruneOurState(state, role)) {
				theScore[0] = getOurPrunedScore(state, role);
				break;
			}
			//        	System.out.println(System.currentTimeMillis());
			if (SystemCalls.passedTime(finishBy)) return null;
			nDepth++;
			state = getOurNextState(state, getOurRandomJointMove(state));
		}
		if(theDepth != null)
			theDepth[0] = nDepth;
		return state;
	}
	
	public List<Move> getOurRandomJointMove(OurMachineState state) throws MoveDefinitionException
	{
		List<Move> random = new ArrayList<Move>();
		for (Role role : getRoles()) {
			random.add(getOurRandomMove(state, role));
		}

		return random;
	}

	public Move getOurRandomMove(OurMachineState state, Role role) throws MoveDefinitionException
	{
		List<Move> legals = getOurLegalMoves(state, role);
		return legals.get(new Random().nextInt(legals.size()));
	}
	
	public List<List<Move>> getOurLegalJointMoves(OurMachineState state) throws MoveDefinitionException
	{
		List<List<Move>> legals = new ArrayList<List<Move>>();
		for (Role role : getRoles()) {
			legals.add(getOurLegalMoves(state, role));
		}

		List<List<Move>> crossProduct = new ArrayList<List<Move>>();
		crossProductLegalMoves(legals, crossProduct, new LinkedList<Move>());

		return crossProduct;
	}

	public List<List<Move>> getOurLegalJointMoves(OurMachineState state, Role role, Move move) throws MoveDefinitionException
	{
		List<List<Move>> legals = new ArrayList<List<Move>>();
		for (Role r : getRoles()) {
			if (r.equals(role)) {
				List<Move> m = new ArrayList<Move>();
				m.add(move);
				legals.add(m);
			} else {
				legals.add(getOurLegalMoves(state, r));
			}
		}

		List<List<Move>> crossProduct = new ArrayList<List<Move>>();
		crossProductLegalMoves(legals, crossProduct, new LinkedList<Move>());

		return crossProduct;
	}
	
	public int getOurPrunedScore(OurMachineState state, Role role) {
		SetOurBasePropositions(state);
		for (Proposition p: trueLatchesToRequiringGoals.keySet()) {
			if (p.getValue() && trueLatchesToRequiringGoals.get(p).get(role) != null) {
				return extractGoalNodeScore(trueLatchesToRequiringGoals.get(p).get(role));
			}
		}
		int uninhibited = propNet.getGoalPropositions().get(role).size();
		Proposition lastUninhibited = null;
		for (Proposition p: trueLatchesToInhibitedGoals.keySet()) {
			if (trueLatchesToInhibitedGoals.get(p).get(role) != null) {
				if (p.getValue()) {
					uninhibited--;
				} else {
					lastUninhibited = p;
				}
			}
			if (p.getValue() && trueLatchesToInhibitedGoals.get(p).get(role) != null) {
				return extractGoalNodeScore(trueLatchesToInhibitedGoals.get(p).get(role));
			}
		}
		if (uninhibited == 1) {
			System.out.println("THIS ALSO SHOULDN'T BE");
			return extractGoalNodeScore(lastUninhibited);
		}
		System.out.println("ERROR WITH PRUNED SCORE");
		return 0;
	}

}
