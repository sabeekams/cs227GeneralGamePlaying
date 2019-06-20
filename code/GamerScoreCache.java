package player.gamer.statemachine.cs227b;

import java.util.HashMap;
import util.statemachine.MachineState;

public class GamerScoreCache {
	private static final double memoryThreshold = 0.2;
	// current score for each State
	private HashMap<MachineState, Double> scoreCache;
	private HashMap<MachineState, Double> secondScoreCache;
	
	public GamerScoreCache() {
		scoreCache = new HashMap<MachineState, Double>();
		secondScoreCache = new HashMap<MachineState, Double>();
	}
	
	public boolean moreThanPercentMemoryAvailable(double threshold) {
		double totalMemory = (double)Runtime.getRuntime().totalMemory();
		double freeMemory = (double)Runtime.getRuntime().freeMemory();
		
		return (freeMemory / totalMemory) > threshold;
	}
	
	public void putScoreFromState(MachineState state, double score) {
		scoreCache.put(state, score);
	}
	
	public double getScoreFromState(MachineState state) {
		return scoreCache.get(state);
	}

	public void doPerMoveWork() {
		if (!moreThanPercentMemoryAvailable(memoryThreshold)) {
			scoreCache = secondScoreCache;
			secondScoreCache = new HashMap<MachineState, Double>();
			System.out.println("ScoreCache size = " + scoreCache.values().size());
		}
	}
}
