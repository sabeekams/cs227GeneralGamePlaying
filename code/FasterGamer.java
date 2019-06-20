package player.gamer.statemachine.cs227b;

import java.util.HashMap;
import java.util.List;

import player.gamer.statemachine.StateMachineGamer;
import util.statemachine.Move;
import util.statemachine.StateMachine;
import util.statemachine.exceptions.GoalDefinitionException;
import util.statemachine.exceptions.MoveDefinitionException;
import util.statemachine.exceptions.TransitionDefinitionException;

public class FasterGamer extends StateMachineGamer {
	protected StateMachineCache<OurMachineState, Double> terminalScoreCache;
	protected StateMachineCache<OurMachineState, Double> heuristicScoreCache;
	private static final double betaValue = 100;
	private static final double alphaValue = 0;
	protected static final int initialIterDepth = 1;
	protected static long useHeuristicTimeThreshold = 2000;
	private int[] dummyDepth = new int[1];
	private OurMachineState ourCurrentState;

	public FasterGamer() {
		super();
	}

	@Override
	public String getName() {
		return "FasterGamer";
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {
		terminalScoreCache = new StateMachineCache<OurMachineState, Double>();
		heuristicScoreCache = new StateMachineCache<OurMachineState, Double>();
		// Search the graph
		stateMachineSelectMove(timeout);
	}

	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {
		long finishBy = timeout - 2000;
		FasterPropNetStateMachine theMachine = (FasterPropNetStateMachine) getStateMachine();
		ourCurrentState = theMachine.convertMachineState(getCurrentState());
		List<Move> myMoves = theMachine.getOurLegalMoves(ourCurrentState, getRole());		
		boolean haveChoices = myMoves.size() > 1;
		
		// Get Monte Carlo scores
		HashMap<Move, Double> movesToMonteCarloScores = new HashMap<Move, Double>();
		if (haveChoices) {
			movesToMonteCarloScores = GetMonteCarloScores(
					(timeout + System.currentTimeMillis() - 2000) / 2);
		}
		
		Move bestMove = myMoves.get(0);
		double bestScore = Double.MIN_VALUE;		
		HashMap<Move, Double> movesToScore = new HashMap<Move, Double>();
		if (myMoves.size() == 1 && !SystemCalls.isMemoryAvailable()) {
			terminalScoreCache.swapCaches();
		}
		int iterDepth = initialIterDepth;
		boolean bailout = false;
		boolean someNonTerminalScores = true;
		while (someNonTerminalScores) {
			someNonTerminalScores = false;
			for (Move move: myMoves) {
				List<List<Move>>jointMoves = theMachine.getOurLegalJointMoves(ourCurrentState, getRole(), move);
				double minScore = Double.MAX_VALUE;
				for (List<Move> jointMove : jointMoves) {
					OurMachineState next = theMachine.getOurNextState(ourCurrentState, jointMove);
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
			if (score == 1 && haveChoices) {
				Double monteCarloScore = movesToMonteCarloScores.get(move);
				if (monteCarloScore != null) score = movesToMonteCarloScores.get(move);
			}
			if (score == bestScore) {
				if (Math.random() > 0.3) {
					bestMove = move;
					bestScore = score;
				}
			}
			if (score > bestScore) {
				bestMove = move;
				bestScore = score;
			}
			//System.out.println("bestMove: " + bestMove + " bestScore: " + bestScore + " move: " + move + " score: " + score);
		}
		//System.out.println("Iteration depth: " + iterDepth);
		//report(bestMove, timeout);
		System.out.println("Time left = " + (timeout - System.currentTimeMillis()));
		return bestMove;
	}
	
	public HashMap<Move, Double> GetMonteCarloScores (long finishBy) 
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {
		FasterPropNetStateMachine theMachine = (FasterPropNetStateMachine) getStateMachine();
		List<Move> myMoves = theMachine.getOurLegalMoves(ourCurrentState, getRole());		
		HashMap<Move, Double> movesToScore = new HashMap<Move, Double>();
		HashMap<Move, Double> movesToTrials = new HashMap<Move, Double>();
		for (Move move: myMoves) {
			movesToScore.put(move, 0.0);
			movesToTrials.put(move, 0.0);
		}
		while(true) {
			for (Move move: myMoves) {
				List<List<Move>>jointMoves = theMachine.getOurLegalJointMoves(ourCurrentState, getRole(), move);
				for (List<Move> jointMove : jointMoves) {
					OurMachineState next = theMachine.getOurNextState(ourCurrentState, jointMove);
					int theScore[] = new int[1];
					OurMachineState terminalState = theMachine.performOurDepthCharge(next, getRole(), dummyDepth, theScore, finishBy);
					if (terminalState == null) {
						for (Move m: myMoves) {
							double trials = movesToTrials.get(m);
							if (trials > 0) {
								double score = movesToScore.get(m) / movesToTrials.get(m);
								score = Math.max(Math.min(score, 99), 1);
								movesToScore.put(m, score);
								//System.out.println(" move: " + m + " score: " + movesToScore.get(m) + " trials: " + movesToTrials.get(m));
							}
						}
						return movesToScore;
					}
					double score = theMachine.getOurGoal(terminalState, getRole());
					movesToScore.put(move, movesToScore.get(move) + score);
					movesToTrials.put(move, movesToTrials.get(move) + 1);
				}
			}
		}
	}

	public void report(Move movePlayed, long timeout) {
		System.out.println("----");
		System.out.println("Gamer = " + getName());
		System.out.println("Role = " + getRole());
		System.out.println("Move played = " + movePlayed);
		System.out.println("Memory usage (bytes) = " + SystemCalls.getUsedMemoryBytes());
		System.out.println("Memory usage (ratio) = " + SystemCalls.getUsedMemoryRatio());
		System.out.println("Terminal Score Cache");
		terminalScoreCache.report();
		System.out.println("Time left = " + (timeout - System.currentTimeMillis()));
		if (timeout - System.currentTimeMillis() < 0)
			System.out.println("WARNING: OUT OF TIME");
		System.out.println("----");
	}

	public double getStateValue(OurMachineState state, long finishBy, double alpha, double beta, int depth, int maxDepth, boolean[] isFinalValue) {
		if (SystemCalls.passedTime(finishBy)) return -1;
		isFinalValue[0] = true;
		
		Double cachedScore = terminalScoreCache.retrieve(state);
		if (cachedScore != null) {
			return cachedScore;
		}

		try {	
			double result;
			FasterPropNetStateMachine theMachine = (FasterPropNetStateMachine) getStateMachine();
			if (theMachine.isOurTerminal(state)) {
				isFinalValue[0]  = true;
				result = theMachine.getOurGoal(state, getRole());
			} else if (theMachine.pruneOurState(state, getRole())) {
				result = theMachine.getOurPrunedScore(state, getRole());
			} else if (depth == maxDepth) {
				isFinalValue[0]  = false;
				Double heuristicScore = heuristicScoreCache.retrieve(state);
				if (heuristicScore == null) {
					heuristicScore = getHeuristicScore(state, finishBy);
					heuristicScoreCache.cache(state, heuristicScore);
				}
				result = heuristicScore;
			} else {
				List<Move> myMoves = theMachine.getOurLegalMoves(state, getRole());
				double maxScore = Double.MIN_VALUE;
				for (Move move : myMoves) {
					List<List<Move>> jointMoves = theMachine.getOurLegalJointMoves(state, getRole(), move);
					double minScore = Double.MAX_VALUE;
					double thisBeta = beta;
					for (List<Move> jointMove : jointMoves) {
						if (SystemCalls.passedTime(finishBy)) return -1;
						OurMachineState next = theMachine.getOurNextState(state, jointMove);
						boolean[] nextFinalValue = new boolean[1];
						double score = getStateValue(next, finishBy, alpha, thisBeta, depth + 1, maxDepth, nextFinalValue) * 0.999;
						if (score < 0) return -1;
						// If the retrieved score didn't get cached, then it's a non-terminal score.
						// The non-terminal score property bubbles up to parents.
						if (!nextFinalValue[0]) {
							isFinalValue[0] = false;
						}
						if (score < minScore) minScore = score;
						if (minScore < thisBeta) {
							thisBeta = minScore;
							if (thisBeta <= alpha) {
								result = thisBeta;
								break;
							}
						}
					}
					if (minScore > maxScore) maxScore = minScore;
					if (maxScore > alpha) {
						alpha = maxScore;
						if (alpha >= beta) {
							result = alpha;
							break;
						}
					}
				}
				result = maxScore;
			}
			if (isFinalValue[0]) {
				terminalScoreCache.cache(state, result);
			} else {
				heuristicScoreCache.cache(state, result);
			}
			return result;
		} catch (Exception e) {
			return -1;
		}
	}
	
	public double getHeuristicScore(OurMachineState state, long finishBy) throws MoveDefinitionException {
		return 1;
	}

	public void stateMachineStop() {
	}

	public void stateMachineAbort() {
	}

	@Override
	public StateMachine getInitialStateMachine() {
		return new FasterPropNetStateMachine();
	}

}
