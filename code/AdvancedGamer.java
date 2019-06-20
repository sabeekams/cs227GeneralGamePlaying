package player.gamer.statemachine.cs227b;

public class AdvancedGamer extends HeuristicGamer {
	
	@Override
	public String getName() {
		return "AdvancedGamer";
	}
	
	protected double oneStepMobilityHeuristicWeight = 1.0;
	protected double oneStepFocusHeuristicWeight = 0.0;
	protected double opponentOneStepMobilityHeuristicWeight = 0.0;
	protected double opponentOneStepFocusHeuristicWeight = 1.0;
	protected double monteCarloHeuristicWeight = 0.0;
	protected double medianMinhashMonteCarloHeuristicWeight = 0.0;

}
