package player.gamer.statemachine.cs227b;

import java.util.HashMap;
import java.util.List;
import util.statemachine.MachineState;
import util.statemachine.Move;
import util.statemachine.Role;
import util.statemachine.StateMachine;
import util.statemachine.exceptions.GoalDefinitionException;
import util.statemachine.exceptions.MoveDefinitionException;
import util.statemachine.exceptions.TransitionDefinitionException;

public class AlphaBetaIterativeDeepeningGamer extends MinimaxGamer {
	private HashMap<MachineState, Integer> terminalScoreCache;
	private static final int betaValue = 100;
	private static final int alphaValue = 0;
	private static final int initialIterDepth = 2;
	
	public AlphaBetaIterativeDeepeningGamer() {
		super();
		terminalScoreCache = new HashMap<MachineState, Integer>();
	}
	
	@Override
	public String getName() {
		return "AlphaBetaIterativeDeepeningGamer";
	}
	
	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {
		terminalScoreCache = new HashMap<MachineState, Integer>();
		// Search the graph
		stateMachineSelectMove(timeout);
	}
	
	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {	
		long finishBy = timeout - 2000;
		
		StateMachine theMachine = getStateMachine();
		MachineState currentState = getCurrentState();
		List<Move> myMoves = theMachine.getLegalMoves(currentState, getRole());		
		Move bestMove = myMoves.get(0);
		int bestScore = Integer.MIN_VALUE;
		List<Move> jointMoves = theMachine.getLegalJointMoves(currentState, getRole(), bestMove).get(0);
		int iterDepth = initialIterDepth;
		boolean someNonTerminalScores = true;
		HashMap<Move, Integer> movesToScore = new HashMap<Move, Integer>();
		
		while (someNonTerminalScores) {
			someNonTerminalScores = false;
			for (Move move: myMoves) {
				jointMoves = theMachine.getLegalJointMoves(currentState, getRole(), move).get(0);
				MachineState next = theMachine.getNextState(currentState, jointMoves);
				int score = getStateValue(next, finishBy, alphaValue, betaValue, 1, iterDepth);
				if (score < 0) break;
				if (terminalScoreCache.get(next) == null) someNonTerminalScores = true;
				movesToScore.put(move, score);
			}
			iterDepth++;
		}
				
		for (Move move: movesToScore.keySet()) {
			int score = movesToScore.get(move);
			if (score > bestScore) {
				bestMove = move;
				bestScore = score;
			}
		}
		
		report(bestMove, getRole(), timeout);
		return bestMove;
	}
	
	public void report(Move movePlayed, Role role, long timeout) {
		System.out.println("----");
		System.out.println("Role = " + role);
		System.out.println("Move played = " + movePlayed);
		System.out.println("Memory usage (bytes) = " + SystemCalls.getUsedMemoryBytes());
		System.out.println("Memory usage (ratio) = " + SystemCalls.getUsedMemoryRatio());
		System.out.println("ScoreCache size = " + terminalScoreCache.values().size());
		((CachingProverStateMachine) getStateMachine()).report();
		System.out.println("Time left = " + (timeout - System.currentTimeMillis()));
		System.out.println("----");
	}
	
	public int getStateValue(MachineState state, long finishBy, int alpha, int beta, int depth, int maxDepth) {
		if (timedOut(finishBy)) return -1;
		Integer cachedScore = terminalScoreCache.get(state);
		if (cachedScore != null)
			return cachedScore;
		
		try {
			boolean isTerminalScore = true;
			int result;
			StateMachine theMachine = getStateMachine();
			if (theMachine.isTerminal(state)) {
				isTerminalScore = true;
				result = theMachine.getGoal(state, getRole());
			} else if (depth == maxDepth) {
				isTerminalScore = false;
				// Temporary setting: marginally better than a forced lose
				result = 1;
			} else {
				List<List<Move>> moves = theMachine.getLegalJointMoves(state);
				// Detect if it's our turn or opponent's
				List<Move> myMoves = theMachine.getLegalMoves(state, getRole());
				int minScore = Integer.MAX_VALUE;
				int maxScore = Integer.MIN_VALUE;
				for (int i = 0; i < moves.size(); i++) {
					if (timedOut(finishBy)) return -1;
					MachineState next = theMachine.getNextState(state, moves.get(i));
					// Get cached score if possible
					int score = getStateValue(next, finishBy, alpha, beta, depth + 1, maxDepth);
					// If the retrieved score didn't get cached, then it's a non-terminal score.
					// The non-terminal score property bubbles up to parents.
					if (terminalScoreCache.get(next) == null) isTerminalScore = false;
					// If error or out of time, exit early
					if (score == -1) return -1;
					if (score < minScore) minScore = score;
					if (score > maxScore) maxScore = score;
					// Alpha beta pruning
					if (myMoves.size() > 1) {
						if (maxScore > alpha) {
							alpha = maxScore;
							if (alpha >= beta) {
								result = alpha;
								break;
							}
						}
					} else {
						if (minScore < beta) {
							beta = minScore;
							if (beta <= alpha) {
								result = beta;
								break;
							}
						}
					}
				}
				// If this is our move or an opponent's
				if (myMoves.size() == 1) {
					result = minScore;
				} else {
					result = maxScore;
				}
			}
			if (isTerminalScore) terminalScoreCache.put(state, result);
			return result;
		} catch (Exception e) {
			return -1;
		}
	}	
}
