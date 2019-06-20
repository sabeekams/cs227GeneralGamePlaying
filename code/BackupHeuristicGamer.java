package player.gamer.statemachine.cs227b;

import java.util.HashMap;
import java.util.List;

import player.gamer.statemachine.StateMachineGamer;
import util.statemachine.MachineState;
import util.statemachine.Move;
import util.statemachine.Role;
import util.statemachine.StateMachine;
import util.statemachine.exceptions.GoalDefinitionException;
import util.statemachine.exceptions.MoveDefinitionException;
import util.statemachine.exceptions.TransitionDefinitionException;

public class BackupHeuristicGamer extends StateMachineGamer {
	protected HashMap<MachineState, Integer> scoreCache;
	protected int maxMobilityObserved;
	protected int numPlayers;
	protected static final int depthThreshold = 100;
	protected static final int timeThreshold = 4000;
	protected static final double focusHeuristicFactor = 5.0;
	protected static final double mobilityHeuristicFactor = 12.0;
	protected static final int timeoutThreshold = 2000;
	protected static final int betaValue = 100;
	protected static final int alphaValue = 0;
	
	
	public BackupHeuristicGamer() {
		super();
	}
	
	@Override
	public String getName() {
		return "BackupHeuristicGamer";
	}
	
	public StateMachine getInitialStateMachine() {
		return new CachingProverStateMachine();
	}
	
	@Override
	public void stateMachineStop() {
		// do nothing
	}

	@Override
	public void stateMachineAbort() {
		// do nothing
	}
	
	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {
		long finishBy = timeout - timeoutThreshold;
		scoreCache = new HashMap<MachineState, Integer>();
		maxMobilityObserved = 2;
		numPlayers = getStateMachine().getRoles().size();
		// Search the graph
		getStateValue(getCurrentState(), finishBy, alphaValue, betaValue, 1);
	}
	
	

	
	/*Keeps track of memory and cache
	 */
	public void report(Move movePlayed, Role role, long timeout) {
		System.out.println("----");
		System.out.println("Role = " + role);
		System.out.println("Move played = " + movePlayed);
		System.out.println("Memory usage (bytes) = " + SystemCalls.getUsedMemoryBytes());
		System.out.println("Memory usage (ratio) = " + SystemCalls.getUsedMemoryRatio());
		System.out.println("ScoreCache size = " + scoreCache.values().size());
		((CachingProverStateMachine) getStateMachine()).report();
		System.out.println("Time left = " + (timeout - System.currentTimeMillis()));
		System.out.println("----");
	}
	
	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {		
		long finishBy = timeout - timeoutThreshold;
		
		StateMachine theMachine = getStateMachine();
		List<Move> myMoves = theMachine.getLegalMoves(getCurrentState(), getRole());
		
		Move bestMove = myMoves.get(0);
		List<Move> jointMoves = theMachine.getLegalJointMoves(getCurrentState(), getRole(), bestMove).get(0);
		int bestMaxValue = getStateValue(theMachine.getNextState(getCurrentState(), jointMoves), finishBy, alphaValue, betaValue, 1);
		for (int i = 1; i < myMoves.size(); i++) {
			Move move = myMoves.get(i);
			jointMoves = theMachine.getLegalJointMoves(getCurrentState(), getRole(), move).get(0);
			int maxValue = getStateValue(theMachine.getNextState(getCurrentState(), jointMoves), finishBy, alphaValue, betaValue, 1);
			if (maxValue > bestMaxValue) {
				bestMove = move;
				bestMaxValue = maxValue;
			}
			if (SystemCalls.passedTime(finishBy)) return bestMove;
		}
		report(bestMove, getRole(), timeout);
		
		return bestMove;
	}
	
	/*
	 * 
	 */
	public int getStateValue(MachineState state, long finishBy, int alpha, int beta, int depth) {
		if (SystemCalls.passedTime(finishBy)) return -1;
		
		Integer cachedScore = scoreCache.get(state);
		if (cachedScore != null) {
			return cachedScore.intValue();
		}
		
		try {
			StateMachine theMachine = getStateMachine();
			if (theMachine.isTerminal(state)) {
				
				if (SystemCalls.isMemoryAvailable()) {
					scoreCache.put(state, theMachine.getGoal(state, getRole()));
				}
				return theMachine.getGoal(state, getRole());
			}
			List<List<Move>> moves = theMachine.getLegalJointMoves(state);
			// Detect if it's our turn or opponent's
			List<Move> myMoves = theMachine.getLegalMoves(state, getRole());
			if (maxMobilityObserved < myMoves.size()) maxMobilityObserved = myMoves.size();
			int minScore = Integer.MAX_VALUE;
			int maxScore = Integer.MIN_VALUE;
			for (int i = 0; i < moves.size(); i++) {
				MachineState next = theMachine.getNextState(state, moves.get(i));
				if (SystemCalls.passedTime(finishBy)) return -1;
				// Get cached score if possible
	
				int score;
				boolean usedHeuristic = false;
				if (useHeuristic(finishBy, depth)) {
					score = getHeuristicForState(state, finishBy);
					usedHeuristic = true;
					//System.out.printf("heuristic score: %d\n", score);
				} else {

					score = getStateValue(next, finishBy, alpha, beta, depth+1);
				}
				// If error or out of time, exit early
				if (score < 0) {
					return -1;
				}

				if (!usedHeuristic) {
					if (SystemCalls.isMemoryAvailable()) {
						//scoreCache.put(state, score);
					}
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
	
	public boolean useHeuristic(long finishBy, int depth) {
		return (SystemCalls.passedTime(finishBy - timeThreshold)) || (depth > depthThreshold);
	}
	
	public int getHeuristic(int numMoves, boolean myTurn, MachineState state, long timeLimit) {
		if(myTurn) {
			return (int)(getMobilityHeuristicScore(numMoves) * 100.0);
		} else {
			return (int)(getFocusHeuristicScore(numMoves) * 100.0);
		}
	}
	
	public int getHeuristicForState(MachineState state, long finishBy) {
		StateMachine theMachine = getStateMachine();
		try {
			if (SystemCalls.passedTime(finishBy)) return -1;
			List<Move> myMoves = theMachine.getLegalMoves(state, getRole());
			int numMoves = myMoves.size();
			if (maxMobilityObserved < numMoves) maxMobilityObserved = numMoves;
			if (SystemCalls.passedTime(finishBy)) return -1;
			
			boolean myTurn = true;
			if (numMoves == 1) {
				int totalOpponentMoves = 0;
				for (Role role : theMachine.getRoles()) {
					if (SystemCalls.passedTime(finishBy)) return -1;
					int opponentMoves = theMachine.getLegalMoves(state, role).size();
					if (opponentMoves > 1) {
						myTurn = false;
						totalOpponentMoves += opponentMoves;
					}
				}
				if (myTurn == true) return (int)(100.0 / numPlayers); // everyone has only one move.
				else numMoves = totalOpponentMoves;
			}
			if (SystemCalls.passedTime(finishBy)) return -1;
			return getHeuristic(numMoves, myTurn, state, Math.min(System.currentTimeMillis() + 50, finishBy));
			
		} catch (MoveDefinitionException e) {
			e.printStackTrace();
			return -1;
		}
	}
	
	// returns a score from zero to one.
	public double getMobilityHeuristicScore(int moves) {
		return moves / (moves + mobilityHeuristicFactor);
	}
	
	// returns a score from zero to one.
	public double getFocusHeuristicScore(int moves) {
		return 1.0 - (moves / (moves + focusHeuristicFactor));
	}
	
	// returns a score from zero to one.
	private int[] returnedDepth = new int[1];
	double getMonteCarloHeuristicScore(MachineState state, long timeLimit) {
		if (System.currentTimeMillis() > timeLimit) return 0;
		
	    StateMachine theMachine = getStateMachine();
	    
	    List<Move> moves;
		try {
			moves = theMachine.getLegalMoves(getCurrentState(), getRole());
		} catch (MoveDefinitionException e1) {
			e1.printStackTrace();
			return 0;
		}
	    
	    int[] moveTotalPoints = new int[moves.size()];
		int[] moveTotalAttempts = new int[moves.size()];
		
		for (int i = 0; true; i = (i+1) % moves.size()) {
		    if (System.currentTimeMillis() > timeLimit)
		        break;

		    try {
		    	MachineState finalState = theMachine.performDepthCharge(theMachine.getRandomNextState(state, getRole(), moves.get(i)), returnedDepth);
		    	moveTotalPoints[i] += theMachine.getGoal(finalState, getRole());
		    	moveTotalAttempts[i] += 1;
		    } catch (Exception e) {
		    	e.printStackTrace();
		    	return 0;
		    }
		}
		
		// TODO: use cache to load initial values for total points and attempts
		double totalPoints = 0;
		double numAttempts = 0;
		for (int i = 0; i < moves.size(); i++){
			totalPoints += moveTotalPoints[i];
			numAttempts += moveTotalAttempts[i];
		}
		// TODO: check memory before saving to cache
		// TODO: save total points and attempts to cache by state
		System.out.println("MonteCarlo number of attempts = " + (int) numAttempts);
		return totalPoints / (numAttempts * 100.0);
	}
}
