package player.gamer.statemachine.cs227b;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;

import util.gdl.grammar.Gdl;
import util.propnet.architecture.Component;
import util.propnet.architecture.PropNet;
import util.propnet.architecture.components.Constant;
import util.propnet.architecture.components.Or;
import util.propnet.architecture.components.Proposition;
import util.propnet.factory.OptimizingPropNetFactory;

public class FactoringPropNetStateMachine extends PropNetStateMachine {
	
	private Set<Component> commonNodes;

	public void initialize(List<Gdl> description) {
		
		System.out.println("propNet about to be created");
		try {
			propNet = OptimizingPropNetFactory.create(description);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		System.out.println("propNet created");

		System.out.println("propnet comps: " + propNet.getComponents().size());
		System.out.println("propnet props: " + propNet.getPropositions().size());
		System.out.println("base props: " + propNet.getBasePropositions().size());
		System.out.println("input props: " + propNet.getInputPropositions().size());
		System.out.println("legal props: " + propNet.getLegalPropositions().size());
		System.out.println("goal props: " + propNet.getGoalPropositions().size());

		commonNodes = new HashSet<Component>();
		List<PropNet> factors = FactorPropNet(propNet);
		System.out.println("propNet factored");

		Set<Component> missing = new HashSet<Component>(propNet.getComponents());
		List<Component> extras = new ArrayList<Component>();
		for (PropNet p : factors){
			System.out.println("factor: " + factors.indexOf(p));
			System.out.println("new propnet comps: " + p.getComponents().size());
			System.out.println("new propnet props: " + p.getPropositions().size());
			System.out.println("new base props: " + p.getBasePropositions().size());
			System.out.println("new input props: " + p.getInputPropositions().size());
			System.out.println("new legal props: " + p.getLegalPropositions().size());
			System.out.println("new goal props: " + p.getGoalPropositions().size());
			missing.removeAll(p.getComponents());
			extras.addAll(p.getComponents());
		}
		System.out.println("missing components " + missing);
		for (Component c : propNet.getComponents()) {
			int i = extras.lastIndexOf(c);
			if (i >= 0)
				extras.remove(i);
		}
		List<Component> copy = new ArrayList<Component>(extras);
		for (Component c : copy) {
			if (commonNodes.contains(c)) {
				extras.remove(c);
			}
		}
		System.out.println("extra components " + extras);
		
		if (factors.size() > 1 && missing.isEmpty()) {
			boolean shouldFactor = true;
			// check if only base, input, goal, legal, terminal and constants are duplicated in extras
			/*for (Component c : extras ) {
				if (c instanceof Constant) continue;
				if (c instanceof Proposition && (
						propNet.getBasePropositions().containsValue(c) ||
						propNet.getInputPropositions().containsValue(c)
						)) {
					continue;
				}
				shouldFactor = false;
				break;
			}*/
			
			if (shouldFactor) {
				// pick best factor
				int best = 0;
				/*for (PropNet p : factors) {
					for (Set<Proposition> goals : p.getGoalPropositions().get(getRole())) {
						
					}
				}*/
				
				PropNet p = factors.get(best);
				propNet = p;
				System.out.println("using factor number " + best);
			}
		}

        roles = propNet.getRoles();
        ordering = getOrdering();
        System.out.println("ordering complete. " + ordering.size() + " nodes.");
	}
	
	public List<PropNet> FactorPropNet(PropNet inputPropNet) {
		List<PropNet> propNetFactors = new ArrayList<PropNet>();
		
		Set<Component> components = new HashSet<Component>(inputPropNet.getComponents());
		Set<Proposition> goalPropositions = new HashSet<Proposition>();
		Set<Proposition> legalPropositions = new HashSet<Proposition>();
				
		Collection<Set<Proposition>> goalSets = inputPropNet.getGoalPropositions().values();
		for (Set<Proposition> goalSet : goalSets) {
			goalPropositions.addAll(goalSet);
		}
		
		Collection<Set<Proposition>> legalSets = inputPropNet.getLegalPropositions().values();
		for (Set<Proposition> legalSet : legalSets) {
			legalPropositions.addAll(legalSet);
		}
		
		Set<Component> excludedORNodes = new HashSet<Component>();
		Set<Component> excludedCommonNodes = new HashSet<Component>();
		for (Proposition proposition : legalPropositions) {
			if (proposition.getSingleInput() instanceof Or) {
				excludedORNodes.add(proposition.getSingleInput());
			} else {
				excludedCommonNodes.add(proposition.getSingleInput());
			}
		}
		for (Proposition proposition : goalPropositions) {
			if (proposition.getSingleInput() instanceof Or) {
				excludedORNodes.add(proposition.getSingleInput());
			} else {
				excludedCommonNodes.add(proposition.getSingleInput());
			}
		}
		Component inputToTerminal = inputPropNet.getTerminalProposition().getSingleInput();
		if (inputToTerminal instanceof Or) {
			excludedORNodes.add(inputToTerminal);
		} else {
			excludedCommonNodes.add(inputToTerminal);
		}
		
		Set<Component> seedNodes = new HashSet<Component>();
		for (Component component : excludedORNodes) {
			for (Component c : component.getInputs())
			if (!(c instanceof Constant)) 
				seedNodes.add(c);
		}
		/*for (Proposition proposition : legalPropositions) {
			if (!(proposition.getSingleInput() instanceof Or) && !(proposition.getSingleInput() instanceof Constant)) {
				seedNodes.add(proposition.getSingleInput());
			}
		}
		for (Proposition proposition : goalPropositions) {
			if (!(proposition.getSingleInput() instanceof Or) && !(proposition.getSingleInput() instanceof Constant)) {
				seedNodes.add(proposition.getSingleInput());
			}
		}
		if (!(inputToTerminal instanceof Or) && !(inputToTerminal instanceof Constant)) {
			seedNodes.add(inputToTerminal);
		}*/

		commonNodes.addAll(excludedORNodes);
		commonNodes.addAll(goalPropositions);
		commonNodes.addAll(legalPropositions);
		commonNodes.add(inputPropNet.getTerminalProposition());
		commonNodes.add(inputPropNet.getInitProposition());
		
		System.out.println("seedNodes: "+seedNodes.size());
		System.out.println("excludedORNodes "+excludedORNodes.size());
		System.out.println("excludedCommonNodes "+excludedCommonNodes.size());
		
		Queue<Component> queue = new LinkedList<Component>();
		while (!seedNodes.isEmpty()) {
			System.out.println("--- seedNodes " + seedNodes.size());
			queue.add(seedNodes.iterator().next());
			System.out.println("--- queue " + queue.size() + " " + queue);

			Set<Component> componentsInCluster = new HashSet<Component>();
			while (!queue.isEmpty()) {
				Component current = queue.poll();
				componentsInCluster.add(current);
				components.remove(current);
				seedNodes.remove(current);

				for (Component prev : current.getInputs()) {
					if (components.contains(prev) &&
							!(prev instanceof Constant) &&
							!goalPropositions.contains(prev) &&
							!legalPropositions.contains(prev) &&
							!excludedORNodes.contains(prev) &&
							!excludedCommonNodes.contains(prev) &&
							prev != inputPropNet.getTerminalProposition() &&
							prev != inputPropNet.getInitProposition())
					{
						queue.add(prev);
						components.remove(prev);
						seedNodes.remove(prev);
					}
					assert (components.contains(prev) || componentsInCluster.contains(prev));
				}
				for (Component next : current.getOutputs()) {
					if (components.contains(next) &&
							!(next instanceof Constant) &&
							!goalPropositions.contains(next) &&
							!legalPropositions.contains(next) &&
							!excludedORNodes.contains(next) &&
							!excludedCommonNodes.contains(next) &&
							next != inputPropNet.getTerminalProposition() &&
							next != inputPropNet.getInitProposition())
					{
						queue.add(next);
						components.remove(next);
						seedNodes.remove(next);
					}
					assert (components.contains(next) || componentsInCluster.contains(next));
				}
			}
			
			// add goal, terminal, initial, legal and excluded nodes back in to the cluster
			queue.addAll(componentsInCluster);
			/*for (Component component : components) {
				if (component instanceof Constant) {
					queue.add(component);
					componentsInCluster.add(component);
					commonNodes.add(component);
				}
			}
			while (!queue.isEmpty()) {
				Component current = queue.poll();
				for (Component next : current.getOutputs()) {
					if (!componentsInCluster.contains(next) &&
							(commonNodes.contains(next) ||
							excludedCommonNodes.contains(next))) {
						componentsInCluster.add(next);
						queue.add(next);
					}
				}
			}
			queue.addAll(componentsInCluster);
			while (!queue.isEmpty()) {
				Component current = queue.poll();
				for (Component prev : current.getInputs()) {
					if (!componentsInCluster.contains(prev) &&
							(commonNodes.contains(prev) ||
							excludedCommonNodes.contains(prev))) {
						componentsInCluster.add(prev);
						queue.add(prev);
					}
				}
			}
			queue.add(inputPropNet.getInitProposition());
			while (!queue.isEmpty()) {
				Component current = queue.poll();
				for (Component next : current.getOutputs()) {
					if (!componentsInCluster.contains(next)) {
						componentsInCluster.add(next);
						queue.add(next);
					}
				}
			}*/
			componentsInCluster.addAll(commonNodes);
			componentsInCluster.addAll(excludedCommonNodes);
			for (Component component : components) {
				if (component instanceof Constant) {
					queue.add(component);
					componentsInCluster.add(component);
					commonNodes.add(component);
				}
			}
			while (!queue.isEmpty()) {
				Component current = queue.poll();
				for (Component next : current.getOutputs()) {
					if (!componentsInCluster.contains(next)) {
						componentsInCluster.add(next);
						queue.add(next);
					}
				}
			}
			
			if (!componentsInCluster.isEmpty())
				propNetFactors.add(new PropNet(inputPropNet.getRoles(), componentsInCluster));
			
		}
		
		return propNetFactors;
	}
	
}
