package player.gamer.statemachine.cs227b;

import util.statemachine.StateMachine;

public class MinimaxPropNet extends MinimaxGamer {

	@Override
	public StateMachine getInitialStateMachine() {
		return new PropNetStateMachine();
	}
	@Override
	public String getName() {
		return "MinimaxPropNetGamer";
	}
	
}
