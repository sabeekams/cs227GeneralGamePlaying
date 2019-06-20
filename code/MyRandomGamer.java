package player.gamer.statemachine.cs227b;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import player.gamer.Gamer;
import player.gamer.exception.MetaGamingException;
import player.gamer.exception.MoveSelectionException;
import util.game.Game;
import util.gdl.grammar.GdlProposition;
import util.gdl.grammar.GdlSentence;
import util.logging.GamerLogger;
import util.match.Match;
import util.statemachine.MachineState;
import util.statemachine.Move;
import util.statemachine.Role;
import util.statemachine.StateMachine;
import util.statemachine.exceptions.MoveDefinitionException;
import util.statemachine.exceptions.TransitionDefinitionException;
import util.statemachine.implementation.prover.ProverStateMachine;


public final class MyRandomGamer extends Gamer
{
	private Match match;
	private GdlProposition roleName;
	private Role role;
	private StateMachine stateMachine;
	private MachineState currentState;
	
	public boolean start(String matchId, GdlProposition roleName, Game game, 
			int startClock, int playClock, long receptionTime) throws MetaGamingException {
		if (!ping()) {
	        GamerLogger.logError("GamePlayer", "Got start message while already busy playing a game: ignoring.");
	        return false;
	    }
		this.match = new Match(matchId, startClock, playClock, game);
		this.roleName = roleName;
		this.stateMachine = new ProverStateMachine();
		this.stateMachine.initialize(game.getRules());
        this.role = this.stateMachine.getRoleFromProp(this.roleName);
        this.currentState = this.stateMachine.getInitialState();
		return true;
	}
	
	public GdlSentence play(String matchId, List<GdlSentence> moves, long receptionTime)
			throws MoveSelectionException, TransitionDefinitionException, MoveDefinitionException {
		if (this.getMatch(matchId) == null) {
			GamerLogger.logError("GamePlayer", "Got play message not intended for current game: ignoring.");
			return null;
		}
		if (moves != null) {
			this.match.appendMoves(moves);
		}

		// Find possible moves
		try
		{
			List<GdlSentence> lastMoves = this.match.getMostRecentMoves();
			if (lastMoves != null)
			{
				List<Move> movesList = new ArrayList<Move>();
				for (GdlSentence sentence : lastMoves)
				{
					movesList.add(stateMachine.getMoveFromSentence(sentence));
				}
				this.currentState = stateMachine.getNextState(currentState, movesList);
				this.match.appendState(currentState.getContents());
			}
			// Pick random move
			List<Move> legalMoves = this.stateMachine.getLegalMoves(currentState, this.role);
			Move selection = legalMoves.get(new Random().nextInt(legalMoves.size()));
			
			return selection.getContents();
		}
			
		catch (Exception e)
		{
		    GamerLogger.logStackTrace("GamePlayer", e);
			throw new MoveSelectionException();
		}

	}
	
	public boolean stop(String matchId, List<GdlSentence> moves) {
		if (this.getMatch(matchId) == null) {
			GamerLogger.logError("GamePlayer", "Got stop message not intended for current game: ignoring.");
			return false;
		}
		if(moves != null) {
			this.match.appendMoves(moves);
		}		
		this.match.markCompleted(null);
		this.match = null;
		return true;
	}
	
	public boolean ping() {
		return this.match == null;		
	}
	
	public boolean abort(String matchId) {
		if (this.getMatch(matchId) == null) {
			GamerLogger.logError("GamePlayer", "Got abort message not intended for current game: ignoring.");
			return false;
		}
		this.match = null;
		return true;
	}

	public Match getMatch(String matchId) {
		if (this.match != null && matchId.equals(this.match.getMatchId())) return this.match;
		return null;
	}
	
	public String getName() {
		return "My Random Gamer";
	}

	@Override
	public void abortAll() {
		// TODO Auto-generated method stub
		
	}

}
