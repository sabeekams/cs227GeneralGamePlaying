package player.gamer.statemachine.cs227b;

import java.util.HashMap;
import java.util.List;
import player.gamer.statemachine.StateMachineGamer;
import util.statemachine.MachineState;
import util.statemachine.Move;
import util.statemachine.StateMachine;
import util.statemachine.exceptions.GoalDefinitionException;
import util.statemachine.exceptions.MoveDefinitionException;
import util.statemachine.exceptions.TransitionDefinitionException;

public class DiscountedRewardGamer extends StateMachineGamer {
	private static final int betaValue = 100;
	private static final int alphaValue = 0;
	protected static final int initialIterDepth = 5;
	protected static long useHeuristicTimeThreshold = 2000;
	protected static double discount = 0.999;

	public DiscountedRewardGamer() {
		super();
	}

	@Override
	public String getName() {
		return "DiscountedRewardGamer";
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {

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
		double bestScore = Double.MIN_VALUE;		
		HashMap<Move, Double> movesToScore = new HashMap<Move, Double>();
		int iterDepth = initialIterDepth;
		boolean bailout = false;
		boolean someNonTerminalScores = true;
		while (someNonTerminalScores) {
			someNonTerminalScores = false;
			for (Move move: myMoves) {
				List<List<Move>>jointMoves = theMachine.getLegalJointMoves(currentState, getRole(), move);
				double minScore = Integer.MAX_VALUE;
				for (List<Move> jointMove : jointMoves) {
					MachineState next = theMachine.getNextState(currentState, jointMove);
					boolean[] finalValue = new boolean[1];
					finalValue[0] = false;
					double score = getStateValue(next, finishBy, alphaValue, betaValue, 1, iterDepth, finalValue);
					if (!finalValue[0]) {
						someNonTerminalScores = true;
					}
					if (score < 0) {
						bailout = true;
						break;
					}
					if (score < minScore) minScore = score;
				}
				if (bailout) break;
				movesToScore.put(move, minScore);
			}
			if (bailout) break;
			iterDepth++;
		}

		for (Move move: movesToScore.keySet()) {
			double score = movesToScore.get(move);
			if (score > bestScore) {
				bestMove = move;
				bestScore = score;
			}
			//System.out.println("bestMove: " + bestMove + " bestScore: " + bestScore + " move: " + move + " score: " + score);
		}
		System.out.println("Iteration depth: " + iterDepth);
		report(bestMove, timeout);
		return bestMove;
	}

	public void report(Move movePlayed, long timeout) {
		System.out.println("----");
		System.out.println("Gamer = " + getName());
		System.out.println("Role = " + getRole());
		System.out.println("Move played = " + movePlayed);
		System.out.println("Memory usage (bytes) = " + SystemCalls.getUsedMemoryBytes());
		System.out.println("Memory usage (ratio) = " + SystemCalls.getUsedMemoryRatio());
		System.out.println("Terminal Score Cache");
		System.out.println("Time left = " + (timeout - System.currentTimeMillis()));
		if (timeout - System.currentTimeMillis() < 0)
			System.out.println("WARNING: OUT OF TIME");
		System.out.println("----");
	}

	public double getStateValue(MachineState state, long finishBy, double alpha, double beta, double depth, int maxDepth, boolean[] isFinalValue) {
		if (SystemCalls.passedTime(finishBy)) return -1;
		isFinalValue[0] = true;

		try {
			double result;
			StateMachine theMachine = getStateMachine();
			if (theMachine.isTerminal(state)) {
				isFinalValue[0]  = true;
				result = theMachine.getGoal(state, getRole());
			} else if (depth == maxDepth) {
				isFinalValue[0]  = false;
				Double heuristicScore ;
				heuristicScore = getHeuristicScore(state, finishBy);
				result = heuristicScore;
			} else {
				List<Move> myMoves = theMachine.getLegalMoves(state, getRole());
				double maxScore = Double.MIN_VALUE;
				for (Move move : myMoves) {
					List<List<Move>> jointMoves = theMachine.getLegalJointMoves(state, getRole(), move);
					double minScore = Double.MAX_VALUE;
					for (List<Move> jointMove : jointMoves) {
						if (SystemCalls.passedTime(finishBy)) return -1;
						MachineState next = theMachine.getNextState(state, jointMove);
						boolean[] nextFinalValue = new boolean[1];
						double score = getStateValue(next, finishBy, alpha, beta, depth + 1, maxDepth, nextFinalValue) * discount;
						if (score < 0) return -1;
						
						// If the retrieved score didn't get cached, then it's a non-terminal score.
						// The non-terminal score property bubbles up to parents.
						if (!nextFinalValue[0]) {
							isFinalValue[0] = false;
						}
						if (score < minScore) minScore = score;
						if (minScore < beta) {
							beta = minScore;
							if (beta <= alpha) {
								result = beta;
								//break;
							}
						}
					}
					if (minScore > maxScore) maxScore = minScore;
					if (maxScore > alpha) {
						alpha = maxScore;
						if (alpha >= beta) {
							result = alpha;
							//break;
						}
					}
				}
				result = maxScore;
			}
			return result;
		} catch (Exception e) {
			return -1;
		}
	}

	// Caveat: Total weights for one thread of execution must equal 1.0, e.g.
	// total weights on heuristics for opponent's turn = 0.8, Monte Carlo heuristic weight 0.2
	protected double oneStepMobilityHeuristicWeight = 0.0;
	protected double oneStepFocusHeuristicWeight = 0.0;

	protected double opponentOneStepMobilityHeuristicWeight = 0.0;
	protected double opponentOneStepFocusHeuristicWeight = 0.0;

	protected double monteCarloHeuristicWeight = 0.0;
	protected double medianMinhashMonteCarloHeuristicWeight = 0.0;
	protected double timeFractionForHeuristicComputation = 0.02;

	public double getHeuristicScore(MachineState state, long finishBy) throws MoveDefinitionException {
		double score = 0.01;

		if (oneStepMobilityHeuristicWeight != 0.0 ||
				oneStepFocusHeuristicWeight != 0.0 ||
				opponentOneStepMobilityHeuristicWeight != 0.0 ||
				opponentOneStepFocusHeuristicWeight != 0.0)
		{
			StateMachine theMachine = getStateMachine();
			List<List<Move>> allMoves = theMachine.getLegalJointMoves(state);
			List<Move> myMoves = theMachine.getLegalMoves(state, getRole());

			boolean opponentTurn = (allMoves.size() / myMoves.size()) > 1;

			// TODO: make heuristic calls time out properly
			if (oneStepMobilityHeuristicWeight != 0.0)
				score = score + oneStepMobilityHeuristicWeight * getOneStepMobilityHeuristic(myMoves.size());
			if (oneStepFocusHeuristicWeight != 0.0)
				score = score + oneStepFocusHeuristicWeight * getOneStepFocusHeuristic(myMoves.size());

			if (opponentTurn) {
				if (opponentOneStepMobilityHeuristicWeight != 0.0)
					score = score + opponentOneStepMobilityHeuristicWeight * getOneStepMobilityHeuristic(allMoves.size() / myMoves.size());
				if (opponentOneStepFocusHeuristicWeight != 0.0)
					score = score + opponentOneStepFocusHeuristicWeight * getOneStepFocusHeuristic(allMoves.size() / myMoves.size());
			}
		}

		if (monteCarloHeuristicWeight != 0.0) {
			long timeNow = System.currentTimeMillis();
			if ((finishBy - timeNow) > 5) {
				long stopTime = (long)(timeNow + (finishBy - timeNow) * timeFractionForHeuristicComputation);
				score = score + monteCarloHeuristicWeight * getMonteCarloHeuristic(state, stopTime);
			}
		}

		if (medianMinhashMonteCarloHeuristicWeight != 0.0) {
			long timeNow = System.currentTimeMillis();
			if ((finishBy - timeNow) > 5) {
				long stopTime = (long)(timeNow + (finishBy - timeNow) * timeFractionForHeuristicComputation);
				score = score + medianMinhashMonteCarloHeuristicWeight * getMedianMinhashMonteCarloHeuristic(state, stopTime);
			}
		}

		return Math.round(Math.max(Math.min(score, 0.999),0.001) * 100.0);
	}

	protected static final double oneStepMobilityHeuristicFactor = 4.0;
	protected double getOneStepMobilityHeuristic(int numMoves) {
		return numMoves / (numMoves + oneStepMobilityHeuristicFactor);
	}

	protected static final double oneStepFocusHeuristicFactor = 1.0;
	protected double getOneStepFocusHeuristic(int numMoves) {
		return Math.max(1.0 - numMoves / (numMoves + oneStepFocusHeuristicFactor), 0.0);
	}

	protected long maxMonteCarloRuntime = 200;
	protected double getMonteCarloHeuristic(MachineState state, long stopTime) {
		int totalScore = 0;
		int runs = 0;
		long start = System.currentTimeMillis();
		StateMachine theMachine = getStateMachine();
		int[] dummyDepth = new int[1];
		try {
			while (!SystemCalls.passedTime(stopTime) && !SystemCalls.passedTime(start + maxMonteCarloRuntime)) {
				MachineState terminalState = theMachine.performDepthCharge(state, dummyDepth);
				totalScore += theMachine.getGoal(terminalState, getRole());
				runs++;
			}
		} catch (Exception e) {
			// TODO: What to actually return?
			return -1.0;
		}
		return ((double)totalScore / runs) / 100.0;
	}

	protected long maxMonteCarloAttempts = 100;
	protected int victoryThreshold = 50;
	protected double getMinhashMonteCarloHeuristic(MachineState state, long stopTime) {
		int runs = 0;

		StateMachine theMachine = getStateMachine();
		int[] dummyDepth = new int[1];
		try {
			while (!SystemCalls.passedTime(stopTime) && runs < maxMonteCarloAttempts) {
				MachineState terminalState = theMachine.performDepthCharge(state, dummyDepth);
				int score = theMachine.getGoal(terminalState, getRole());
				if (score > victoryThreshold) break; // check that our score is not smaller then opponents
				runs++;
			}
		} catch (Exception e) {
			// TODO: What to actually return?
			return -1.0;
		}
		return 1.0 - (runs / maxMonteCarloAttempts);
	}

	protected double getMedianMinhashMonteCarloHeuristic(MachineState state, long stopTime) {
		double[] score = new double[3];
		for (int i = 0; i < 3; i++) {
			score[i] = getMinhashMonteCarloHeuristic(state, stopTime);
		}

		if (score[0] > score[1]) {
			if (score[1] > score[2]) {
				return score[1];
			} else if (score[0] > score[2]) {
				return score[2];
			} else {
				return score[0];
			}
		} else {
			if (score[2] > score[1]) {
				return score[1];
			} else if (score[0] > score[2]) {
				return score[0];
			} else {
				return score[2];
			}
		}
	}

	public void stateMachineStop() {
	}

	public void stateMachineAbort() {		
	}

	@Override
	public StateMachine getInitialStateMachine() {
		return new PropNetStateMachine();

	}

}
