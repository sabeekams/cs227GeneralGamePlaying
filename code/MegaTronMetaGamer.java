package player.gamer.statemachine.cs227b;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Random;

import util.statemachine.MachineState;
import util.statemachine.Move;
import util.statemachine.StateMachine;
import util.statemachine.exceptions.GoalDefinitionException;
import util.statemachine.exceptions.MoveDefinitionException;
import util.statemachine.exceptions.TransitionDefinitionException;

public class MegaTronMetaGamer extends HeuristicGamer {
	protected HashMap<MachineState, Integer> endbookScoreCache;
	protected double averageDepth;
	protected double averageWidth;
	protected double myAverageWidth;
	protected double depthChargeAveTime; // in nano-seconds
	protected List<Tuple<Integer, Double>> mobilityScores;
	protected Tuple<Double, Double> linearFunction;
	
	public String getName(){
		//return "MegaTronMetaGamer";
		return "AlwaysPlayScissors-Megatron";
	}
	
	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {
		
		terminalScoreCache = new StateMachineCache<MachineState, Integer>();
		heuristicScoreCache = new StateMachineCache<MachineState, Integer>();
		endbookScoreCache = new HashMap<MachineState, Integer>();
		
		long finishBy = timeout - 2000;
		
		mobilityScores = new ArrayList<Tuple<Integer, Double>>();
		getAverageScorePerMobility(finishBy, 0.33, 8, 8);
		getAverageScorePerMobility(finishBy, 0.25, 8, 8);
		getAverageScorePerMobility(finishBy, 0.22, 8, 8);
		getAverageScorePerMobility(finishBy, 0.175, 8, 8);
		getAverageScorePerMobility(finishBy, 0.165, 8, 8);
		getAverageScorePerMobility(finishBy, 0.15, 8, 8);
		getAverageScorePerMobility(finishBy, 0.125, 8, 8);
		getAverageScorePerMobility(finishBy, 0.1, 8, 8);
		computeMobilityCurve();
		
		averageDepth = getAverageDepth(finishBy, 10);
		averageWidth = getAverageWidth(finishBy, 0.25, 6);
		
		maxMonteCarloAttempts = (long) (25 * 10000000.0 / depthChargeAveTime); // expected # of attempts for 0.25 seconds
		maxMonteCarloRuntime = (long) ((depthChargeAveTime / 1000000.0) * 4.0); // expected time in msec for 5 attempts
		
		System.out.println("average depth: " + averageDepth);
		System.out.println("average width: " + averageWidth);
		System.out.println("my average width: " + myAverageWidth);
		System.out.println("mobility score samples: " + mobilityScores.size());
		System.out.println("average depth charge time: " + depthChargeAveTime / 1000000000.0);
		System.out.println("new max Monte Carlo attempts: " + maxMonteCarloAttempts);
		System.out.println("new max Monte Carlo runtime: " + maxMonteCarloRuntime);
		
		/*for (int i = 0; i < mobilityScores.size(); i++) {
			System.out.println(mobilityScores.get(i).x + ", " + mobilityScores.get(i).y);
		}*/
		System.out.println("linear mobility function = #moves * " + linearFunction.x + " + " + linearFunction.y);
		
		// TODO: use data to set the weights.
		if (maxMonteCarloRuntime <= 200) {
			oneStepMobilityHeuristicWeight = 0.4;
			monteCarloHeuristicWeight = 0.4;
			opponentOneStepFocusHeuristicWeight = 0.2;
		} else {
			oneStepMobilityHeuristicWeight = 0.7;
			monteCarloHeuristicWeight = 0.0;
			opponentOneStepFocusHeuristicWeight = 0.3;
		}
		
		createEndBook(finishBy - 90000);
		
		// Search the graph
		stateMachineSelectMove(timeout);

		report(null, timeout);
	}

	void createEndBook(long finishBy){

		StateMachine theMachine = getStateMachine();
		MachineState currentState = getCurrentState();

		while (!SystemCalls.passedTime(finishBy)) {
			MachineState state = currentState;
			MachineState prev = currentState;

			try {
				while (!theMachine.isTerminal(state) && endbookScoreCache.get(state) == null) {
					prev = state;
					state = theMachine.getNextStateDestructively(prev, theMachine.getRandomJointMove(prev));
				}
				
				if (endbookScoreCache.get(state) != null) {
					endbookScoreCache.put(prev, endbookScoreCache.get(state));
				} else {
					endbookScoreCache.put(prev, theMachine.getGoal(state, getRole()));
				}
				
			} catch (GoalDefinitionException e) {
				e.printStackTrace();
			} catch (TransitionDefinitionException e) {
				e.printStackTrace();
			} catch (MoveDefinitionException e) {
				e.printStackTrace();
			}
			
		}
	}
	
	public double getAverageDepth(long finishBy, int maxSamples){
		
		StateMachine theMachine = getStateMachine();
		MachineState currentState = getCurrentState();

		double depthSum = 0;
		int count = 0;

		try {
			long startTime = System.nanoTime();
			while (!SystemCalls.passedTime(finishBy) && count < maxSamples) {
				int[] depth = new int[1];

				theMachine.performDepthCharge(currentState, depth);
				if (depth != null && depth[0] > 0){
					depthSum += depth[0];
					count++;
				}
			}
			depthChargeAveTime = count > 0 ? (System.nanoTime() - startTime) / count : -1;
		} catch (TransitionDefinitionException e) {
			e.printStackTrace();
		} catch (MoveDefinitionException e) {
			e.printStackTrace();
		}
		return (count > 0) ? (depthSum/count) : -1;
	}
	
	public double getAverageWidth(long finishBy, double prob, int maxSamples){

		double widthSum = 0;
		int count = 0;
		double myWidthSum = 0;
		int myCount = 0;

		while (!SystemCalls.passedTime(finishBy) && count < maxSamples) {
			int[] myWidth = new int[1];
			int width = getWidthAtRandomDepth(finishBy, prob, myWidth);
			widthSum += width;
			count++;
			if (myWidth[0] > 1) {
				myWidthSum += myWidth[0];
				myCount++;
			}
		}
		
		myAverageWidth = myCount > 1 ? myWidthSum / myCount : -1;
		
		return count > 0 ? widthSum/count : -1;
	}
	
	public int getWidthAtRandomDepth(long finishBy, double prob, int[] myWidth) {

		StateMachine theMachine = getStateMachine();
		MachineState state = getCurrentState();
		Random r = new Random();
		
		try {
			while(!SystemCalls.passedTime(finishBy) && r.nextDouble() > prob && !theMachine.isTerminal(state)) {
	            state = theMachine.getNextStateDestructively(state, theMachine.getRandomJointMove(state));
	        }
			List<List<Move>> moves = theMachine.getLegalJointMoves(state);
			int s = 0;
			for (int i = 0; i < moves.size(); i++) {
				s += moves.get(i).size();
			}
			List<Move> myMoves = theMachine.getLegalMoves(state, getRole());
			myWidth[0] = myMoves.size();
			return s;
				
		} catch (TransitionDefinitionException e) {
			e.printStackTrace();
		} catch (MoveDefinitionException e) {
			e.printStackTrace();
		}
		return 0;
	}
	
	/*public void sampleWidthAtAllDepths(long finishBy, int maxSamples) {
		
		while (!SystemCalls.passedTime(finishBy) && count < maxSamples) {
		}
	}*/
	
	public void getAverageScorePerMobility(long finishBy, double prob, int monteCarloSamples, int maxSamples) {

		StateMachine theMachine = getStateMachine();
		Random r = new Random();
		int runs = 0;

		while (!SystemCalls.passedTime(finishBy) && runs < maxSamples) {
			try {
				MachineState state = getCurrentState();
				boolean terminal = theMachine.isTerminal(state);
				while(!SystemCalls.passedTime(finishBy) && r.nextDouble() > prob && !terminal) {
					state = theMachine.getNextStateDestructively(state, theMachine.getRandomJointMove(state));
					terminal = theMachine.isTerminal(state);
				}
				if (terminal) break; // continue; // changed to quit if the search goes too deep.

				List<Move> moves = theMachine.getLegalMoves(state, getRole());
				int numActions =  moves.size();
				
				while (numActions == 1) {
					state = theMachine.getNextStateDestructively(state, theMachine.getRandomJointMove(state));
					terminal = theMachine.isTerminal(state);
					if (terminal) break; // continue; // changed to quit if the search goes too deep.
					moves = theMachine.getLegalMoves(state, getRole());
					numActions =  moves.size();
				}
				if (terminal) break;

				double sumScore = 0;
				int count = 0;
				while (!SystemCalls.passedTime(finishBy) && count < monteCarloSamples) {
					int[] dummyDepth = new int[1];
					MachineState terminalState = theMachine.performDepthCharge(state, dummyDepth);
					sumScore += theMachine.getGoal(terminalState, getRole());
					count++;
				}

				if (count > 0) {
					mobilityScores.add(new Tuple<Integer, Double>(numActions, sumScore / count));
					runs++;
					if (count == monteCarloSamples)
						heuristicScoreCache.cache(state, (int) (sumScore / count));
				}

			} catch (TransitionDefinitionException e) {
				e.printStackTrace();
			} catch (MoveDefinitionException e) {
				e.printStackTrace();
			} catch (GoalDefinitionException e) {
				e.printStackTrace();
			}
		}
	}
	
	public void computeMobilityCurve() {
		double Sx = 0.0;
		double Sy = 0.0;
		double Sxx = 0.0;
		double Sxy = 0.0;
		//double Syy = 0.0;
		double x, y;
		int n = mobilityScores.size();
		
		for(int i = 0; i < n; i++) {
			x = mobilityScores.get(i).x;
			y = mobilityScores.get(i).y;
			Sx += x;
			Sy += y;
			Sxx += x*x;
			Sxy += x*y;
			//Syy += y*y;
		}
		
		double Beta = (n*Sxy - Sx*Sy) / (n*Sxx - Sx*Sx);
		double alpha = Sy/n - (Beta/n)*Sx;
		
		if(Double.isNaN(Beta) || Double.isNaN(alpha) || Double.isInfinite(Beta) || Double.isInfinite(alpha)) { 
			linearFunction = new Tuple<Double, Double>(0.0, Sy/n);
		}
		
		linearFunction = new Tuple<Double, Double>(Beta, alpha);
	}
	
	protected double getOneStepMobilityHeuristic(int numMoves) {
		return Math.max(Math.min((numMoves * linearFunction.x + linearFunction.y) / 100.0, 0.99), 0.01);
	}

	public int getStateValue(MachineState state, long finishBy, int alpha, int beta, int depth, int maxDepth, boolean[] isFinalValue) {
		if (SystemCalls.passedTime(finishBy)) return -1;
		isFinalValue[0] = true;
		
		Integer cachedScore = terminalScoreCache.retrieve(state);
		if (cachedScore != null)
			return cachedScore;

		try {	
			int result;
			StateMachine theMachine = getStateMachine();
			if (theMachine.isTerminal(state)) {
				isFinalValue[0]  = true;
				result = theMachine.getGoal(state, getRole());
			} else if (endbookScoreCache.get(state) !=null && depth >= maxDepth){
				result = endbookScoreCache.get(state);
			} else if (depth == maxDepth) {  // || SystemCalls.passedTime(finishBy - useHeuristicTimeThreshold)) {
				isFinalValue[0]  = false;
				Integer heuristicScore = heuristicScoreCache.retrieve(state);
				if (heuristicScore == null) {
					heuristicScoreCache.cache(state, heuristicScore);
					heuristicScore = getHeuristicScore(state, finishBy);
				} 
				result = heuristicScore;
			} else {
				List<Move> myMoves = theMachine.getLegalMoves(state, getRole());
				int maxScore = Integer.MIN_VALUE;
				for (Move move : myMoves) {
					List<List<Move>> jointMoves = theMachine.getLegalJointMoves(state, getRole(), move);
					int minScore = Integer.MAX_VALUE;
					for (List<Move> jointMove : jointMoves) {
						if (SystemCalls.passedTime(finishBy)) return -1;
						MachineState next = theMachine.getNextState(state, jointMove);
						boolean[] nextFinalValue = new boolean[1];
						int score = getStateValue(next, finishBy, alpha, beta, depth + 1, maxDepth, nextFinalValue);
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
	
	public void report(Move movePlayed, long timeout) {
		System.out.println("----");
		System.out.println("Gamer = " + getName());
		System.out.println("Role = " + getRole());
		System.out.println("Move played = " + movePlayed);
		System.out.println("Memory usage (bytes) = " + SystemCalls.getUsedMemoryBytes());
		System.out.println("Memory usage (ratio) = " + SystemCalls.getUsedMemoryRatio());
		System.out.println("Terminal Score Cache");
		terminalScoreCache.report();
		((CachingProverStateMachine) getStateMachine()).report();
		System.out.println("End Book Cache Size = " + endbookScoreCache.size());
		System.out.println("Time left = " + (timeout - System.currentTimeMillis()));
		if (timeout - System.currentTimeMillis() < 0)
			System.out.println("WARNING: OUT OF TIME");
		System.out.println("----");
	}
}

