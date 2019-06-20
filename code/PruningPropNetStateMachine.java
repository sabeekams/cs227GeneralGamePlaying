package player.gamer.statemachine.cs227b;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;

import util.gdl.grammar.GdlConstant;
import util.gdl.grammar.GdlFunction;
import util.propnet.architecture.Component;
import util.propnet.architecture.PropNet;
import util.propnet.architecture.components.And;
import util.propnet.architecture.components.Constant;
import util.propnet.architecture.components.Not;
import util.propnet.architecture.components.Or;
import util.propnet.architecture.components.Proposition;
import util.propnet.architecture.components.Transition;

public class PruningPropNetStateMachine extends CachingPropNetStateMachine {

	private Set<Component> commonNodes;
	private List<PropNet> factors;
	
	public void propagateConstants() {
		System.out.println("===== Before propagating constants =====");
		System.out.println("propnet comps: " + propNet.getComponents().size());
		System.out.println("propnet props: " + propNet.getPropositions().size());
		System.out.println("base props: " + propNet.getBasePropositions().size());
		System.out.println("input props: " + propNet.getInputPropositions().size());
		System.out.println("legal props: " + propNet.getLegalPropositions().size());
		System.out.println("goal props: " + propNet.getGoalPropositions().size());
		
		Set<Component> components = new HashSet<Component>(propNet.getComponents());
		Set<Constant> constantComponents = new HashSet<Constant>();
		
		for (Component c : components) {
			if (c instanceof Constant) {
				constantComponents.add((Constant) c);
			}
		}
		
		// <child, parent> tuple
		Queue<Tuple<Component,Component>> childrenOfConstants = new LinkedList<Tuple<Component,Component>>();
		for (Constant constant : constantComponents) {
			for (Component child : constant.getOutputs()) {
				childrenOfConstants.add(new Tuple<Component,Component>(child, constant));
			}
			
			while (!childrenOfConstants.isEmpty()) {
				Tuple<Component,Component> child = childrenOfConstants.poll(); // handle one <child,parent> tuple at a time
				
				if (child.x instanceof And) {  // handle And nodes
					if (child.y.getValue()) {
						// unlink parent and child
						child.y.removeOutput(child.x);
						child.x.removeInput(child.y);
						
						if (child.x.getInputs().isEmpty()) { // replace child with True Constant
							// add a new constant to the propNet
							Constant newConstant = new Constant(true);
							propNet.addComponent(newConstant);
							
							// replace child with new constant node
							for (Component grandChild : child.x.getOutputs()) {
								
								// link new constant and grand child
								newConstant.addOutput(grandChild);
								grandChild.addInput(newConstant);
								
								// unlink child and grand child
								grandChild.removeInput(child.x);
								child.x.removeOutput(grandChild);
								
								// add grand child to children of constants list.
								childrenOfConstants.add(new Tuple<Component,Component>(grandChild, newConstant));
							}
							
							// remove the child from the propNet
							propNet.removeComponent(child.x);
						}
					} else {
						// add a new constant to the propNet
						Constant newConstant = new Constant(false);
						propNet.addComponent(newConstant);
						
						// replace child with new constant node
						for (Component grandChild : child.x.getOutputs()) {
							
							// link new constant and grand child
							newConstant.addOutput(grandChild);
							grandChild.addInput(newConstant);
							
							// unlink child and grand child
							grandChild.removeInput(child.x);
							child.x.removeOutput(grandChild);
							
							// add grand child to children of constants list.
							childrenOfConstants.add(new Tuple<Component,Component>(grandChild, newConstant));
						}
						
						// unlink parent and child
						child.y.removeOutput(child.x);
						child.x.removeInput(child.y);
						
						// remove the child from the propNet
						propNet.removeComponent(child.x);
					}
				} else if (child.x instanceof Or) { // handle Or Nodes
					if (child.y.getValue()) {
						// add a new constant to the propNet
						Constant newConstant = new Constant(true);
						propNet.addComponent(newConstant);
						
						// replace child with new constant node
						for (Component grandChild : child.x.getOutputs()) {
							
							// link new constant and grand child
							newConstant.addOutput(grandChild);
							grandChild.addInput(newConstant);
							
							// unlink child and grand child
							grandChild.removeInput(child.x);
							child.x.removeOutput(grandChild);
							
							// add grand child to children of constants list.
							childrenOfConstants.add(new Tuple<Component,Component>(grandChild, newConstant));
						}
						
						// unlink parent and child
						child.y.removeOutput(child.x);
						child.x.removeInput(child.y);
						
						// remove the child from the propNet
						propNet.removeComponent(child.x);
					} else {
						// unlink parent and child
						child.y.removeOutput(child.x);
						child.x.removeInput(child.y);
						
						if (child.x.getInputs().isEmpty()) { // replace child with False Constant
							// add a new constant to the propNet
							Constant newConstant = new Constant(false);
							propNet.addComponent(newConstant);
							
							// replace child with new constant node
							for (Component grandChild : child.x.getOutputs()) {
								
								// link new constant and grand child
								newConstant.addOutput(grandChild);
								grandChild.addInput(newConstant);
								
								// unlink child and grand child
								grandChild.removeInput(child.x);
								child.x.removeOutput(grandChild);
								
								// add grand child to children of constants list.
								childrenOfConstants.add(new Tuple<Component,Component>(grandChild, newConstant));
							}
							
							// remove the child from the propNet
							propNet.removeComponent(child.x);
						}
					}
				} else if (child.x instanceof Not) {
					// add a new constant to the propNet
					Constant newConstant = new Constant(!child.y.getValue());
					propNet.addComponent(newConstant);
					
					// replace child with new constant node
					for (Component grandChild : child.x.getOutputs()) {
						
						// link new constant and grand child
						newConstant.addOutput(grandChild);
						grandChild.addInput(newConstant);
						
						// unlink child and grand child
						grandChild.removeInput(child.x);
						child.x.removeOutput(grandChild);
						
						// add grand child to children of constants list.
						childrenOfConstants.add(new Tuple<Component,Component>(grandChild, newConstant));
					}
					
					// unlink parent and child
					child.y.removeOutput(child.x);
					child.x.removeInput(child.y);
					
					// remove the child from the propNet
					propNet.removeComponent(child.x);
				} else if (child.x instanceof Transition) {
					if (child.y.getValue() && child.x.getInputs().size() > 1) {
						// unlink parent and child
						child.x.removeInput(child.y);
						child.y.removeOutput(child.x);
					}
				} else if (child.x instanceof Proposition) {
					// check if child is a special node.  (legal, goal, terminal, input, base)
					Proposition proposition = (Proposition) child.x;

					if (proposition.getInputs().size() == 1 && proposition.getSingleInput() instanceof Transition) {
						// base prop
					} else if (proposition.getName() instanceof GdlFunction) {
						GdlFunction function = (GdlFunction) proposition.getName();
						if (function.getName().getValue().equals("goal")) {
							// goal prop
						} else if (function.getName().getValue().equals("legal")) {
							// legal prop
						} else if (function.getName().getValue().equals("does")) {
							// input prop
						}
					} else if ( proposition.getName() instanceof GdlConstant ) {
						GdlConstant gdlConstant = (GdlConstant) proposition.getName();
						if ( gdlConstant.getValue().equals("terminal") ) {
							// terminal prop
						} else if (gdlConstant.getValue().equals("INIT")) {
							// initial prop
						} 
					} else {
						// regular prop
						
						// add a new constant to the propNet
						Constant newConstant = new Constant(child.y.getValue());
						propNet.addComponent(newConstant);
						
						// replace child with new constant node
						for (Component grandChild : child.x.getOutputs()) {
							
							// link new constant and grand child
							newConstant.addOutput(grandChild);
							grandChild.addInput(newConstant);
							
							// unlink child and grand child
							grandChild.removeInput(child.x);
							child.x.removeOutput(grandChild);
							
							// add grand child to children of constants list.
							childrenOfConstants.add(new Tuple<Component,Component>(grandChild, newConstant));
						}
						
						// unlink parent and child
						child.y.removeOutput(child.x);
						child.x.removeInput(child.y);
						
					}
					
				} else if (child.x instanceof Constant) {
					// shouldn't actually happen
					// unlink parent and child
					child.x.removeInput(child.y);
					child.y.removeOutput(child.x);
				}
				
				// remove parent from propNet if it has no more children
				if (child.y.getOutputs().isEmpty()) {
					propNet.removeComponent(child.y);
				}
			}
		}
	}
	
	public void removeDuplicateNodes() {
		System.out.println("===== Before removing duplicate nodes =====");
		System.out.println("propnet comps: " + propNet.getComponents().size());
		System.out.println("propnet props: " + propNet.getPropositions().size());
		System.out.println("base props: " + propNet.getBasePropositions().size());
		System.out.println("input props: " + propNet.getInputPropositions().size());
		System.out.println("legal props: " + propNet.getLegalPropositions().size());
		System.out.println("goal props: " + propNet.getGoalPropositions().size());
		
		List<Component> components = new ArrayList<Component>(propNet.getComponents());
		Set<Tuple<Component,Component>> pairs = new HashSet<Tuple<Component,Component>>();
		int size = components.size();
		
		for (int i = 0; i < size; i++) {
			for (int j = i+1; j < size; j++) {
				if (components.get(i).getClass() == (components.get(j)).getClass()) {
					if (components.get(i).getInputs() == components.get(j).getInputs()) {
						if (components.get(i).getOutputs() == components.get(j).getOutputs()) {
							pairs.add(new Tuple<Component,Component>(components.get(i), components.get(j)));
						}
					}
				}
			}
		}

		for (Tuple<Component,Component> pair : pairs) {
			if (propNet.getComponents().contains(pair.y)) {
				// remove pair.y from propNet
				for (Component prev : pair.y.getInputs()) {
					prev.removeOutput(pair.y);
				}
				for (Component next : pair.y.getOutputs()) {
					next.removeInput(pair.y);
				}
				propNet.removeComponent(pair.y);
			}
		}
	}
	
	public void getFactors() {
		System.out.println("===== Before Factoring =====");
		System.out.println("propnet comps: " + propNet.getComponents().size());
		System.out.println("propnet props: " + propNet.getPropositions().size());
		System.out.println("base props: " + propNet.getBasePropositions().size());
		System.out.println("input props: " + propNet.getInputPropositions().size());
		System.out.println("legal props: " + propNet.getLegalPropositions().size());
		System.out.println("goal props: " + propNet.getGoalPropositions().size());
		
		commonNodes = new HashSet<Component>();
		factors = FactorPropNet(propNet);
		System.out.println("===== PropNet factored =====");

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
			boolean shouldKeepFactors = true;
			// check that only base, input, goal, legal, terminal and constants are duplicated in extras
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
			
			if (shouldKeepFactors) {
				// pick best factor
				/*int best = 0;
				for (PropNet p : factors) {
					for (Set<Proposition> goals : p.getGoalPropositions().get(getRole())) {
						
					}
				}
				
				propNet = factors.get(best);
				System.out.println("using factor number " + best);*/
			} else {
				factors = new ArrayList<PropNet>();
				factors.add(propNet);
				System.out.println("not using factors");
			}
		} else {
			factors = new ArrayList<PropNet>();
			factors.add(propNet);
			System.out.println("not using factors");
		}
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

		commonNodes.addAll(excludedORNodes);
		commonNodes.addAll(excludedCommonNodes);
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
					if (!componentsInCluster.contains(next) && commonNodes.contains(next)) {
						componentsInCluster.add(next);
						queue.add(next);
					}
				}
			}
			queue.addAll(componentsInCluster);
			while (!queue.isEmpty()) {
				Component current = queue.poll();
				if (propNet.getBasePropositions().containsValue(current)) {
					for (Component prev : current.getInputs()) {
						if (!componentsInCluster.contains(prev)) {
							componentsInCluster.add(prev);
							queue.add(prev);
						}
					}
				}
			}
			/*queue.add(inputPropNet.getInitProposition());
			while (!queue.isEmpty()) {
				Component current = queue.poll();
				for (Component next : current.getOutputs()) {
					if (!componentsInCluster.contains(next)) {
						componentsInCluster.add(next);
						queue.add(next);
					}
				}
			}*/
			
			// alternative implementation
			/*componentsInCluster.addAll(commonNodes);
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
			}*/
			
			if (!componentsInCluster.isEmpty())
				propNetFactors.add(new PropNet(inputPropNet.getRoles(), componentsInCluster));
			
		}
		
		return propNetFactors;
	}
	
}
