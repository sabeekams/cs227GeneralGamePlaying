package player.gamer.statemachine.cs227b;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import util.gdl.grammar.Gdl;
import util.gdl.grammar.GdlFunction;
import util.gdl.grammar.GdlSentence;
import util.gdl.grammar.GdlTerm;
import util.propnet.architecture.Component;
import util.propnet.architecture.PropNet;
import util.propnet.architecture.components.Proposition;
import util.propnet.factory.OptimizingPropNetFactory;
import util.statemachine.MachineState;
import util.statemachine.Move;
import util.statemachine.Role;
import util.statemachine.StateMachine;
import util.statemachine.exceptions.GoalDefinitionException;
import util.statemachine.exceptions.MoveDefinitionException;
import util.statemachine.exceptions.TransitionDefinitionException;

public class PropNetStateMachine extends StateMachine {
	/** The underlying proposition network  */
    protected PropNet propNet;
    /** The topological ordering of the propositions */
    protected List<Proposition> ordering;
    protected List<Proposition> terminalOrdering;
    protected List<Proposition> nextStateOrdering;
    protected Map<Role, List<Proposition>> legalOrderings;
    protected Map<Role, List<Proposition>> goalOrderings;
    /** The player roles */
    protected List<Role> roles;
    //private Map<Proposition, Integer> coercedScores;
    // Variables for optimization
    //private Map<String, Proposition> trueGoals;
    protected Map<String, ArrayList<Proposition>> trueLegals;
    protected Set<Proposition> unorderedProps;
    // Variables for pruning
    protected Set<Proposition> trueLatches;
    protected Set<Proposition> falseLatches;
    protected ImplicationGraph implicationGraph;
    protected Map<Proposition, Map<Role, Proposition>> trueLatchesToRequiringGoals;
    protected Map<Proposition, Map<Role, Proposition>> falseLatchesToRequiringGoals;
    protected Map<Proposition, Map<Role, Proposition>> trueLatchesToInhibitedGoals;
    protected Map<Proposition, Map<Role, Proposition>> falseLatchesToInhibitedGoals;
    // Caches
    
	@Override
	public void initialize(List<Gdl> description) {
		System.out.println(description);
		
		try {
			propNet = OptimizingPropNetFactory.create(description);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
        System.out.println("Finished initializing propnet");
        roles = propNet.getRoles();
        additionalInit();
        
        //trueGoals = new HashMap<String, Proposition>();
        trueLegals = new HashMap<String, ArrayList<Proposition>>();
        for (Role role: roles) {
        	trueLegals.put(role.toString(), new ArrayList<Proposition>());
        }
        unorderedProps = new HashSet<Proposition>();
		for (Proposition p: propNet.getBasePropositions().values()) {
			unorderedProps.add(p);
		}
		for (Proposition p: propNet.getInputPropositions().values()) {
			unorderedProps.add(p);
		}
		unorderedProps.add(propNet.getInitProposition());
		
        propagateConstants();
        removeDuplicateNodes();
        //getFactors();
		
        ordering = getOrdering();
        setOptimizedOrderings();
        
        initializeImplicationGraph();
        initializeLatches();
        initializeLatchGoals();
//        for (Proposition p: propNet.getPropositions()) {
//        	if (p.getName().toString().indexOf("cell 8 8") >= 0) {
//        		System.out.println(p);
//        		System.out.println(p.getInputs());
//        		System.out.println(p.getSingleInput().getInputs());
//        		System.out.println(p.getSingleInput().getSingleInput().getInputs());
//        		System.out.println(p.getSingleInput().getSingleInput().getSingleInput().getInputs());
//        	}
//        	if (p.getName().toString().indexOf("does black ( drop 8 )") >= 0) {
//        		System.out.println(p);
//        		for (Component out: p.getOutputs()) {
//        			System.out.println(out);
//        			for (Component out2: out.getOutputs()) {
//            			System.out.println(out2);
//            			for (Component out3: out2.getOutputs()) {
//            				System.out.println(out3);
//            				System.out.println(out3.getSingleOutput());
//            				System.out.println(out3.getSingleOutput().getOutputs());
//            			}
//        			}
//        		}
//        	}
//        }
        
        
//        initializeCoercedScores();
//    	Set<Proposition> linkedGoals = new HashSet<Proposition>();
//    	Proposition goal = null;
//    	for (Set<Proposition> set : propNet.getGoalPropositions().values()) {
//    		for (Proposition p: set) {
//    			goal = p;
//    			break;
//    		}
//    		break;
//    	}
//    	fillLinkedGoals(linkedGoals, goal, new HashMap<Component>());
//        System.out.println(linkedGoals);
    }

	public void additionalInit() {
	}
	public void propagateConstants() {
	}
	public void removeDuplicateNodes() {
	}
	public void getFactors() {
	}
	
	public List<Proposition> getOrdering() {	
		List<Proposition> ordering = new ArrayList<Proposition>();
		Set<Proposition> satisfied = new HashSet<Proposition>();
//		Set<Proposition> propositions = propNet.getPropositions();
		Stack<Proposition> toProcess = new Stack<Proposition>();
		Map<Proposition, Set<Proposition>> propsToUnsatisfiedInputs = new HashMap<Proposition, Set<Proposition>>();
		for (Proposition p: propNet.getPropositions()) {
			Set<Proposition> unsatisfiedInputs = getPropositionInputs(p);
			if (!unorderedProps.contains(p)) propsToUnsatisfiedInputs.put(p, unsatisfiedInputs);
			if (unsatisfiedInputs.size() == 0) {
				// Push propositions based on constants to the stack
				toProcess.push(p);
			}
		}
		for (Proposition p: unorderedProps) toProcess.push(p);
		
//		int count = 0;
		while (!toProcess.isEmpty()) {
//			count++;
//			if (count > 100) break;
//			if (count % 1000 == 0) {
//				System.out.println("LA");
//				System.out.println(toProcess.size());
//				System.out.println(satisfied.size());
//				System.out.println(ordering.size());
//			}
			Proposition p = toProcess.pop();
//			System.out.println(c);
			boolean inputsSatisfied = true;
			if (!unorderedProps.contains(p)) {
				Set<Proposition> satisfiedInputs = new HashSet<Proposition>();
				Set<Proposition> unsatisfiedInputs = propsToUnsatisfiedInputs.get(p);
				for (Proposition in: unsatisfiedInputs) {
					if (satisfied.contains(in)) {
						satisfiedInputs.add(in);
					} else {
						inputsSatisfied = false;
						break;
					}
				}
				for (Proposition sat: satisfiedInputs) unsatisfiedInputs.remove(sat);
			}
			if (inputsSatisfied) {
				satisfied.add(p);
				if (!unorderedProps.contains(p)) ordering.add(p);
				for (Proposition out: getPropositionOutputs(p)) {
					if (!satisfied.contains(out) && !unorderedProps.contains(out)) toProcess.push(out);
				}
			}
		}
//		for (Proposition p: ordering) System.out.println("ORDERING " + p);
		return ordering;
	}
	
	public void setOptimizedOrderings() {
		terminalOrdering = new ArrayList<Proposition>();
		nextStateOrdering = new ArrayList<Proposition>();
		legalOrderings = new HashMap<Role, List<Proposition>>();
		goalOrderings = new HashMap<Role, List<Proposition>>();

		Set<Proposition> terminalInputs = getAllDependencies(propNet.getTerminalProposition());
		Set<Proposition> anons = new HashSet<Proposition>();
		for (Proposition base: propNet.getBasePropositions().values()) {
			for (Proposition p: getPropositionInputs(base)) anons.add(p);
		}
		Set<Proposition> nextStateInputs = getAllDependencies(anons);
		
		Map<Role, Set<Proposition>> allLegalInputs = new HashMap<Role, Set<Proposition>>();
		Map<Role, Set<Proposition>> allGoalInputs = new HashMap<Role, Set<Proposition>>();
		for (Role role: roles) {
			legalOrderings.put(role, new ArrayList<Proposition>());
			goalOrderings.put(role, new ArrayList<Proposition>());
			Set<Proposition> legalInputs = getAllDependencies(propNet.getLegalPropositions().get(role));
			Set<Proposition> goalInputs = getAllDependencies(propNet.getGoalPropositions().get(role));
			allLegalInputs.put(role, legalInputs);
			allGoalInputs.put(role, goalInputs);
		}
		for (Proposition p: ordering) {
			if (terminalInputs.contains(p)) terminalOrdering.add(p);
			if (nextStateInputs.contains(p)) nextStateOrdering.add(p);
			for (Role role: roles) {
				if (allLegalInputs.get(role).contains(p)) legalOrderings.get(role).add(p);
				if (allGoalInputs.get(role).contains(p)) goalOrderings.get(role).add(p);
			}
		}
	}
	
	private Set<Proposition> getPropositionOutputs(Proposition p) {
		Set<Proposition> outputs = new HashSet<Proposition>();
		Stack<Component> toProcess = new Stack<Component>();
		for (Component out: p.getOutputs()) toProcess.push(out);
		while (!toProcess.isEmpty()) {
			Component c = toProcess.pop();
			if (c instanceof Proposition) {
				outputs.add((Proposition)c);
			} else {
				for (Component out: c.getOutputs()) toProcess.push(out);
			}
		}
		return outputs;
	}
	
	private Set<Proposition> getPropositionInputs(Proposition p) {
		Set<Proposition> inputs = new HashSet<Proposition>();
		Stack<Component> toProcess = new Stack<Component>();
		for (Component in: p.getInputs()) toProcess.push(in);
		while (!toProcess.isEmpty()) {
			Component c = toProcess.pop();
			if (c instanceof Proposition) {
				inputs.add((Proposition)c);
			} else {
				for (Component in: c.getInputs()) toProcess.push(in);
			}
		}
		return inputs;
	}
	
	private Set<Proposition> getAllDependencies(Proposition p) {
		Collection<Proposition> props = new ArrayList<Proposition>();
		props.add(p);
		return getAllDependencies(props);
	}
	
	private Set<Proposition> getAllDependencies(Collection<Proposition> props) {
		Set<Proposition> dependencies = new HashSet<Proposition>();
		Stack<Component> toProcess = new Stack<Component>();
		for (Proposition p: props) toProcess.push(p);
		while (!toProcess.isEmpty()) {
			Component c = toProcess.pop();
			if (c instanceof Proposition) {
				dependencies.add((Proposition)c);
			}
			if (!unorderedProps.contains(c))
				for (Component in: c.getInputs()) if (!dependencies.contains(in)) toProcess.push(in);
		}
		return dependencies;
	}

	private void initializeImplicationGraph() {
		implicationGraph = new ImplicationGraph(propNet.getPropositions(), propNet.getLegalInputMap());
	}
	
	private void initializeLatches() {
		trueLatches = new HashSet<Proposition>();
		falseLatches = new HashSet<Proposition>();
		Collection<Proposition> basePropositions = propNet.getBasePropositions().values();
		for (Set<ImplicationGraph.Node> scc: implicationGraph.sccs) {
			Set<ImplicationGraph.Node> baseNodes = new HashSet<ImplicationGraph.Node>();
			for (ImplicationGraph.Node n: scc) {
				if (basePropositions.contains(n.proposition)) {
					baseNodes.add(n);
				}
			}
			if (baseNodes.size() == 1) {
				for (ImplicationGraph.Node n: baseNodes) {
					if (n.value) {
						trueLatches.add(n.proposition);
					} else {
						falseLatches.add(n.proposition);
					}
				}
			}
		}
		System.out.println("TRUE LATCHES: " + trueLatches.size());
		System.out.println("FALSE LATCHES: " + falseLatches.size());
	}

	public void initializeLatchGoals() {
		trueLatchesToRequiringGoals = new HashMap<Proposition, Map<Role, Proposition>>();
		falseLatchesToRequiringGoals = new HashMap<Proposition, Map<Role, Proposition>>();
		trueLatchesToInhibitedGoals = new HashMap<Proposition, Map<Role, Proposition>>();
		falseLatchesToInhibitedGoals = new HashMap<Proposition, Map<Role, Proposition>>();
		for (Proposition latch: trueLatches) {
			for (Role role: roles) {
				for (Proposition goal: propNet.getGoalPropositions().get(role)) {
					ImplicationGraph.Node trueLatchNode = implicationGraph.getNode(latch, true);
					ImplicationGraph.Node falseLatchNode = implicationGraph.getNode(latch, false);
					ImplicationGraph.Node trueGoalNode = implicationGraph.getNode(goal, true);
					ImplicationGraph.Node falseGoalNode = implicationGraph.getNode(goal, false);
					if (implicationGraph.implies(trueLatchNode, trueGoalNode,
							trueLatchNode, new HashSet<ImplicationGraph.Node>())) {
						if (trueLatchesToRequiringGoals.get(latch) == null) {
							trueLatchesToRequiringGoals.put(latch, new HashMap<Role, Proposition>());
						}
						trueLatchesToRequiringGoals.get(latch).put(role, goal);
					}
					if (implicationGraph.implies(falseLatchNode, trueGoalNode,
							falseLatchNode, new HashSet<ImplicationGraph.Node>())) {
						if (falseLatchesToRequiringGoals.get(latch) == null) {
							falseLatchesToRequiringGoals.put(latch, new HashMap<Role, Proposition>());
						}
						falseLatchesToRequiringGoals.get(latch).put(role, goal);
					}
					if (implicationGraph.implies(trueLatchNode, falseGoalNode,
							trueLatchNode, new HashSet<ImplicationGraph.Node>())) {
						if (trueLatchesToInhibitedGoals.get(latch) == null) {
							trueLatchesToInhibitedGoals.put(latch, new HashMap<Role, Proposition>());
						}
						trueLatchesToInhibitedGoals.get(latch).put(role, goal);
					}
				}
			}
		}
		System.out.println("True latches as goal requirements: " + trueLatchesToRequiringGoals.size());
		System.out.println("False latches as goal requirements: " + falseLatchesToRequiringGoals.size());
		System.out.println("True latches as goal inhibitors: " + trueLatchesToInhibitedGoals.size());
		System.out.println("False latches as goal inhibitors: " + falseLatchesToInhibitedGoals.size());
	}
	
	protected int extractGoalNodeScore(Proposition p) {
		GdlFunction func = (GdlFunction)p.getName();
		return Integer.parseInt(func.getBody().get(1).toString());
	}
	
	public int getPrunedScore(MachineState state, Role role) {
		SetBasePropositions(state);
		for (Proposition p: trueLatchesToRequiringGoals.keySet()) {
			if (p.getValue() && trueLatchesToRequiringGoals.get(p).get(role) != null) {
				return extractGoalNodeScore(trueLatchesToRequiringGoals.get(p).get(role));
			}
		}
		int uninhibited = propNet.getGoalPropositions().get(role).size();
		Proposition lastUninhibited = null;
		for (Proposition p: trueLatchesToInhibitedGoals.keySet()) {
			if (trueLatchesToInhibitedGoals.get(p).get(role) != null) {
				if (p.getValue()) {
					uninhibited--;
				} else {
					lastUninhibited = p;
				}
			}
			if (p.getValue() && trueLatchesToInhibitedGoals.get(p).get(role) != null) {
				return extractGoalNodeScore(trueLatchesToInhibitedGoals.get(p).get(role));
			}
		}
		if (uninhibited == 1) {
			System.out.println("THIS ALSO SHOULDN'T BE");
			return extractGoalNodeScore(lastUninhibited);
		}
		System.out.println("ERROR WITH PRUNED SCORE");
		return 0;
	}

	public boolean pruneState(MachineState state, Role role) {
		if (trueLatchesToRequiringGoals.size() >= 1 || falseLatchesToRequiringGoals.size() >= 1) {
			SetBasePropositions(state);
			for (Proposition p: trueLatchesToRequiringGoals.keySet()) {
				if (p.getValue() && trueLatchesToRequiringGoals.get(p).get(role) != null) {
					return true;
				}
			}
			int uninhibited = propNet.getGoalPropositions().get(role).size();
			for (Proposition p: trueLatchesToInhibitedGoals.keySet()) {
				if (p.getValue() && trueLatchesToInhibitedGoals.get(p).get(role) != null) {
					uninhibited--;
				}
			}
			if (uninhibited == 1) {
				System.out.println("THIS SHOULDN'T BE");
				return true;
			}
		}
		return false;
	}
	
	@Override
	public int getGoal(MachineState state, Role theRole)
			throws GoalDefinitionException {
		SetBasePropositions(state);
//		System.out.println("NEW " + theRole);
		Propagate(goalOrderings.get(theRole));
//		System.out.println(trueGoals.values());
//		Propagate(ordering);
//		System.out.println("OLD");
//		System.out.println(trueGoals.values());
		for (Proposition goal: propNet.getGoalPropositions().get(theRole)) {
			if (goal.getValue()) return extractGoalNodeScore(goal);
		}
		System.out.println("ERROR GETTING GOAL");
		return 0;

//		int roleScore = 0;
//		int maxOpponentScore = Integer.MIN_VALUE;
//		String theRoleName = theRole.toString();
//		
//		for (String role: trueGoals.keySet()) {
//			GdlFunction func = (GdlFunction)trueGoals.get(role).getName();
//			int score = Integer.parseInt(func.getBody().get(1).toString());
//			if (role == theRoleName) {
//				roleScore = score;
//			} else {
//				maxOpponentScore = Math.max(maxOpponentScore, score);
//			}
//		}
//		int result = 0;
//		if (roleScore < maxOpponentScore) {
//			result = 0;
//		} else if (roleScore == maxOpponentScore) {
//			result = 50;
//		} else {
//			result = 100;
//		}
//		return result;
	}

	@Override
	public boolean isTerminal(MachineState state) {
//		Timer t = new Timer();
		SetBasePropositions(state);
		Propagate(terminalOrdering);
//		t.stop();
//		Timer.report();
		return propNet.getTerminalProposition().getValue();
	}

	@Override
	public List<Role> getRoles() {
		return roles;
	}

	@Override
	public MachineState getInitialState() {
		Set<GdlSentence> contents = new HashSet<GdlSentence>();
		propNet.getInitProposition().setValue(true);
		for (Proposition p: propNet.getBasePropositions().values()) {
			if (p.getSingleInput().getValue()) {
				contents.add(p.getName().toSentence());
			}
			p.setValue(p.getSingleInput().getValue());
		}
		MachineState result = new MachineState(contents);
		return result;
	}

	@Override
	public List<Move> getLegalMoves(MachineState state, Role role)
			throws MoveDefinitionException {
		List<GdlSentence> moves = new ArrayList<GdlSentence>();
		SetBasePropositions(state);
		Propagate(legalOrderings.get(role));
		for (Proposition p: propNet.getLegalPropositions().get(role)) {
			if (p.getValue()) {
				GdlFunction func = (GdlFunction)p.getName();
				moves.add(func.getBody().get(1).toSentence());
			}
		}
//		System.out.println("MOVES SIZE " + moves.size());
//		System.out.println(state);
//		for (Proposition p: propNet.getLegalPropositions().get(roles.get(0))) {
//			System.out.println(p.getValue());
//			System.out.println(p.getSingleInput().getValue());
//			System.out.println(p);
//			System.out.println(p.getInputs());
//			System.out.println(p.getSingleInput().getInputs());
//		}
		return Move.gdlToMoves(moves);
	}

	@Override
	public MachineState getNextState(MachineState state, List<Move> moves)
			throws TransitionDefinitionException {
		Set<GdlSentence> contents = new HashSet<GdlSentence>();
		SetBasePropositions(state);
		SetInputPropositions(moves);
		Propagate(nextStateOrdering);
		
		for (Proposition p: propNet.getBasePropositions().values()) {
 			if (p.getSingleInput().getValue()) {
				contents.add(p.getName().toSentence());
			}
		}
		return new MachineState(contents);
	}
	
	private void SetBasePropositions(MachineState state) {
		// (Julius) Put this line somewhere else?
		propNet.getInitProposition().setValue(false);

		Set<GdlSentence> contents = state.getContents();

		for (Proposition p: propNet.getBasePropositions().values()) {
			if (contents.contains(p.getName().toSentence())) {
				p.setValue(true); 
			} else {
				p.setValue(false);
			}
		}
	}
	
	protected void SetInputPropositions(List<Move> moves) {
		// Make a map of the player roles to each of the passed moves. This works under
		// the assumption that the passed moves and getRoles() are ordered in the same way.
		Map<GdlTerm, GdlTerm> roleToMoves = new HashMap<GdlTerm, GdlTerm>();
		for (int i = 0; i < moves.size(); i++) {
			GdlTerm roleTerm = getRoles().get(i).getName().toTerm();
			GdlTerm moveTerm = moves.get(i).getContents().toTerm();
			roleToMoves.put(roleTerm, moveTerm);
		}
		Map<GdlTerm, Proposition> inputPropositions = propNet.getInputPropositions();
		for (GdlTerm term: inputPropositions.keySet()) {
			GdlFunction func = (GdlFunction)term;
			List<GdlTerm> body = func.getBody();
			inputPropositions.get(term).setValue(roleToMoves.get(body.get(0)) == body.get(1));
		}
	}
	
	protected void Propagate(List<Proposition> anOrdering) {
		for (Proposition p: anOrdering) {
			p.setValue(p.getSingleInput().getValue());
		}
	}
	
	// Depth charge with timeout
    public MachineState performDepthCharge(MachineState state, Role role, int[] theDepth, int[] theScore, long finishBy) throws TransitionDefinitionException, MoveDefinitionException {  
    	int nDepth = 0;
        while(true) {
        	if (isTerminal(state)) {
        		try {
					theScore[0] = getGoal(state, role);
				} catch (GoalDefinitionException e) {
					e.printStackTrace();
				}
        		break;
        	} else if (pruneState(state, role)) {
        		theScore[0] = getPrunedScore(state, role);
        		break;
        	}
//        	System.out.println(System.currentTimeMillis());
        	if (SystemCalls.passedTime(finishBy)) return null;
            nDepth++;
            state = getNextStateDestructively(state, getRandomJointMove(state));
        }
        if(theDepth != null)
            theDepth[0] = nDepth;
        return state;
    }
        
    /*private boolean isGoalNode(Component c) {
		return (c instanceof Proposition &&
				((Proposition)c).getName() instanceof GdlFunction &&
				(((GdlFunction)((Proposition)c).getName()).getName().getValue().equals("goal")));
    }
    
    private boolean isLegalNode(Proposition p) {
		return (p.getName() instanceof GdlFunction &&
				((GdlFunction)p.getName()).getName().getValue().equals("legal"));
    }*/
}
