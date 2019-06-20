package player.gamer.statemachine.cs227b;

public class PessimisticGamer extends HeuristicGamer {
	
	@Override
	public String getName() {
		return "PessimisticGamer";
	}
	
	protected double oneStepMobilityHeuristicWeight = 0.3;
	protected double oneStepFocusHeuristicWeight = 0.0;
	protected double opponentOneStepMobilityHeuristicWeight = 0.0;
	protected double opponentOneStepFocusHeuristicWeight = 0.0;
	protected double monteCarloHeuristicWeight = 0.0;
	protected double medianMinhashMonteCarloHeuristicWeight = 0.6;
	
	//protected long maxMonteCarloRuntime = 50;
	protected long maxMonteCarloAttempts = 10;
	protected static final double oneStepMobilityHeuristicFactor = 5.0;
	protected static final double opponentOneStepFocusHeuristicFactor = 1.0;
	
}
