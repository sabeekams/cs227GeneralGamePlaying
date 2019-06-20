package player.gamer.statemachine.cs227b;

import java.util.HashMap;
import java.util.List;
import util.statemachine.MachineState;
import util.statemachine.Move;
import util.statemachine.StateMachine;
import util.statemachine.exceptions.GoalDefinitionException;
import util.statemachine.exceptions.MoveDefinitionException;
import util.statemachine.exceptions.TransitionDefinitionException;

public class AlphaBetaGamer extends MinimaxGamer {
	private HashMap<MachineState, Integer> scoreCache;
	
	public AlphaBetaGamer() {
		super();
		scoreCache = new HashMap<MachineState, Integer>();
	}
	
	@Override
	public String getName() {
		return "AlphaBetaGamer";
	}
	
	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {
		long finishBy = timeout - 2000;
		scoreCache = new HashMap<MachineState, Integer>();
		// Search the graph
		getStateValue(getCurrentState(), finishBy, Integer.MIN_VALUE, Integer.MAX_VALUE);
	}
	
	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {	
		long finishBy = timeout - 2000;
		
		StateMachine theMachine = getStateMachine();
		List<Move> myMoves = theMachine.getLegalMoves(getCurrentState(), getRole());
		
		Move bestMove = myMoves.get(0);
		List<Move> jointMoves = theMachine.getLegalJointMoves(getCurrentState(), getRole(), bestMove).get(0);
		int bestMaxValue = getStateValue(theMachine.getNextState(getCurrentState(), jointMoves), finishBy, Integer.MIN_VALUE, Integer.MAX_VALUE);
		for (int i = 1; i < myMoves.size(); i++) {
			Move move = myMoves.get(i);
			jointMoves = theMachine.getLegalJointMoves(getCurrentState(), getRole(), move).get(0);
			int maxValue = getStateValue(theMachine.getNextState(getCurrentState(), jointMoves), finishBy, Integer.MIN_VALUE, Integer.MAX_VALUE);
			if (maxValue > bestMaxValue) {
				bestMove = move;
				bestMaxValue = maxValue;
			}
			if (timedOut(finishBy)) return bestMove;
		}
		System.out.println(SystemCalls.getFreeMemoryRatio());
		return bestMove;
	}
	
	public void dumpScoreCache() {
		for (MachineState s: scoreCache.keySet()) {
			System.out.println(s.toString() + ": " + scoreCache.get(s));
		}
	}
	
	public int getStateValue(MachineState state, long finishBy, int alpha, int beta) {
		if (timedOut(finishBy)) return -1;
		Integer cachedScore = scoreCache.get(state);
		if (cachedScore != null)
			return cachedScore;
		
		try {
			StateMachine theMachine = getStateMachine();
			if (theMachine.isTerminal(state)) {
				scoreCache.put(state, theMachine.getGoal(state, getRole()));
				return theMachine.getGoal(state, getRole());
			}
			List<List<Move>> moves = theMachine.getLegalJointMoves(state);
			// Detect if it's our turn or opponent's
			List<Move> myMoves = theMachine.getLegalMoves(state, getRole());
			int minScore = Integer.MAX_VALUE;
			int maxScore = Integer.MIN_VALUE;
			for (int i = 0; i < moves.size(); i++) {
				if (timedOut(finishBy)) return -1;
				MachineState next = theMachine.getNextState(state, moves.get(i));
				// Get cached score if possible
				int score = getStateValue(next, finishBy, alpha, beta);
				// If error or out of time, exit early
				if (score == -1) {
					return -1;
				}
				if (score < minScore) minScore = score;
				if (score > maxScore) maxScore = score;
				if (myMoves.size() > 1) {
					if (maxScore > alpha) {
						alpha = maxScore;
						if (alpha >= beta) {
							scoreCache.put(state, alpha);
							return alpha;
						}
					}
				} else {
					if (minScore < beta) {
						beta = minScore;
						if (beta <= alpha) {
							scoreCache.put(state, beta);
							return beta;
						}
					}
				}
			}
			// If this is our move or an opponent's
			if (myMoves.size() == 1) {
				scoreCache.put(state, minScore);
				return minScore;
			} else {
				scoreCache.put(state, maxScore);
				return maxScore;
			}

		} catch (Exception e) {
			return -1;
		}
	}	
}
