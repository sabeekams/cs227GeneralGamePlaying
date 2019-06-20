package player.gamer.statemachine.cs227b;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import util.propnet.architecture.Component;
import util.propnet.architecture.components.And;
import util.propnet.architecture.components.Not;
import util.propnet.architecture.components.Or;
import util.propnet.architecture.components.Proposition;
import util.propnet.architecture.components.Transition;

public class NecessityGraph {
	private Set<Node> nodes;
	private Map<Proposition, Node> trueNodes;
	private Map<Proposition, Node> falseNodes;
	public Set<Set<Node>> sccs;
	
	public NecessityGraph(Collection<Proposition> propositions) {
		nodes = new HashSet<Node>();
		trueNodes = new HashMap<Proposition, Node>();
		falseNodes = new HashMap<Proposition, Node>();
		for (Proposition p: propositions) {
			Node n = new Node(p, true);
			nodes.add(n);
			trueNodes.put(p, n);
			n = new Node(p, false);
			nodes.add(n);
			falseNodes.put(p, n);
		}
		for (Node n: nodes) {
			fillEdgesForProposition(n, n.proposition, n.value);
		}
//		for (Node n: trueNodes.values()) {
//			System.out.println("NODE");
//			System.out.println(n);
//			System.out.println(n.outputs);
//		}
		findSccs();
//		for (Set<Node> scc: sccs) {
//			System.out.println("SCC");
//			for (Node n: scc) {
//				System.out.println(n);
//			}
//		}
	}
	
	private void fillEdgesForProposition(Node n, Component current, boolean truth) {
		for (Component c: current.getOutputs()) {
			if (c instanceof Proposition) {
				if (truth) {
					n.outputs.add(trueNodes.get((Proposition)c));
				} else {
					n.outputs.add(falseNodes.get((Proposition)c));
				}
			} else if (c instanceof And) {
				if (!truth) fillEdgesForProposition(n, c, truth);
			} else if (c instanceof Or) {
				if (truth) fillEdgesForProposition(n, c, truth);
			} else if (c instanceof Not) {
				fillEdgesForProposition(n, c, !truth);
			} else if (c instanceof Transition) {
				fillEdgesForProposition(n, c, truth);
			}
		}
	}
	
	// Find strongly connected components via Tarjan's algorithm.
	private void findSccs() {
		sccs = new HashSet<Set<Node>>();
		Map<Node, Integer> indices = new HashMap<Node, Integer>();
		Map<Node, Integer> lowlinks = new HashMap<Node, Integer>();
		Stack<Node> stack = new Stack<Node>();
		int index[] = new int[1];
		index[0] = 0;
		for (Node n: nodes) {
			if (indices.get(n) == null) {
				strongConnect(n, sccs, indices, lowlinks, stack, index);				
			}
		}
	}
	
	// Helper for findCycles
	private void strongConnect(Node n, Set<Set<Node>> sccs, Map<Node, Integer> indices,
			Map<Node, Integer> lowlinks, Stack<Node> stack, int[] index) {
		indices.put(n, index[0]);
		lowlinks.put(n, index[0]);
		index[0]++;
		stack.push(n);
		for (Node output: n.outputs) {
			if (indices.get(output) == null) {
				strongConnect(output, sccs, indices, lowlinks, stack, index);
				lowlinks.put(n, Math.min(lowlinks.get(n), lowlinks.get(output)));
			} else if (stack.contains(output)) {
				lowlinks.put(n, Math.min(lowlinks.get(n), indices.get(output)));
			}
		}
		if (indices.get(n).intValue() == lowlinks.get(n).intValue()){
			Set<Node> scc = new HashSet<Node>();
			while (stack.peek() != n) {
				scc.add(stack.pop());
			}
			scc.add(stack.pop());
			if (scc.size() > 1) sccs.add(scc);
		}
	}
	

	public static class Node {
		public Proposition proposition;
		public boolean value;
		public Set<Node> outputs;
		
		public Node(Proposition p, boolean v) {
			proposition = p;
			value = v;
			outputs = new HashSet<Node>();
		}
		
		public int hashCode() {
			return (proposition.toString() + value).hashCode();
		}
		
		public String toString() {
			return (value + " " + proposition.toString());
		}
	}
}