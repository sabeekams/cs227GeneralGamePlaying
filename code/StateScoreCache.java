package player.gamer.statemachine.cs227b;

import java.util.HashMap;
import util.statemachine.MachineState;

public class StateScoreCache {
	// current score for each State
	private HashMap<MachineState, Double> scoreCache;
	private HashMap<MachineState, Double> secondScoreCache;
	
	public StateScoreCache() {
		scoreCache = new HashMap<MachineState, Double>();
		secondScoreCache = new HashMap<MachineState, Double>();
	}
	
	public void putScoreFromState(MachineState state, double score) {
		if (SystemCalls.isMemoryAvailable()) 
			scoreCache.put(state, score);
	}
	
	public double getScoreFromState(MachineState state) {
		Double score = scoreCache.get(state);
		if (score == null) {
			return -1.0;
		} else {
			secondScoreCache.put(state, score);
		}
		return score;
	}

	public void SwapCachesIfNeeded() {
		if (!SystemCalls.isMemoryAvailable()) {
			scoreCache = secondScoreCache;
			secondScoreCache = new HashMap<MachineState, Double>();
			System.out.println("ScoreCache size = " + scoreCache.values().size());
		}
	}
}
