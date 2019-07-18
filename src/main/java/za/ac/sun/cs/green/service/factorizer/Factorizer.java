/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.factorizer;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import org.apache.logging.log4j.Logger;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Operation.Operator;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Compute the factors of an expression.
 * 
 * This implementation uses a union find data structure (<a href=
 * "http://en.wikipedia.org/wiki/Disjoint-set_data_structure">Disjoint-set data
 * structure</a>).
 */
public class Factorizer {

	/**
	 * The Java {@link Logger} associated with the {@link Green} solver.
	 */
	protected final Logger log;

	/**
	 * Construct an instance of a factorizer.
	 *
	 * @param log logger
	 */
	public Factorizer(Logger log) {
		this.log = log;
	}

	/**
	 * Report statistics gathered during factorization.
	 *
	 * @param reporter mechanism through which reporting is done
	 */
	public void report(Reporter reporter) {
	}

	/**
	 * Factorize an expression. This is accomplished by traversing the expression,
	 * and grouping the propositions found based on the variables they contain.
	 *
	 * @param expression expression to factorize
	 * @return set of factors
	 */
	public Set<Expression> factorize(Expression expression) {
		CollectionVisitor collector = new CollectionVisitor();
		try {
			expression.accept(collector);
		} catch (VisitorException x) {
			log.fatal("encountered an exception -- this should not be happening!", x);
		}
		final Map<Expression, Expression> factors = new HashMap<>();
		DisjointSet<Expression> disjointSet = collector.getDisjointSet();
		for (Expression proposition : disjointSet.getElements()) {
			Expression root = disjointSet.find(proposition);
			factors.merge(root, proposition, (e1, e2) -> new Operation(Operator.AND, e1, e2));
		}
		return new HashSet<Expression>(factors.values());
	}

	// ======================================================================
	//
	// VISITOR TO COLLECT PROPOSITIONS AND MAP THEM TO SETS OF VARIABLES
	//
	// ======================================================================

	/**
	 * Visitor that traverses an expression, picks up propositions, and groups.
	 */
	private static class CollectionVisitor extends Visitor {

		/**
		 * Disjoint-set of propositions.
		 */
		private final DisjointSet<Expression> disjointSet = new DisjointSet<>();

		/**
		 * Map each variable to the representative proposition for the factor in which
		 * the variable appears.
		 */
		private final Map<Variable, Expression> rootMap = new HashMap<>();

		/**
		 * The current proposition being explored. This is set when, as be traverse down
		 * the expression tree, we encounter -- for the first time -- an operator that
		 * is not "and".
		 */
		private Expression currentProposition = null;

		/**
		 * Current depth of the traversal. This is needed to handle nested "and"
		 * operations and also "and" operations nested inside "or" operations.
		 * 
		 * For example, given
		 * 
		 * <pre>
		 * ((x == 0) && (y == 1)) && ((z == 0) && (q + 1 == 2))
		 * </pre>
		 * 
		 * the whole expression is depth 0, and so is the
		 * <code>((x==0) && (y==1))</code> and <code>((z==2) && (q+1==3))</code>
		 * subexpressions. The expressions <code>(x==0)</code>, <code>(y==1)</code>,
		 * <code>(z==0)</code>, and <code>(q+1==2)</code> are depth 1, the expressions
		 * <code>x</code>, <code>y</code>, <code>z</code>, <code>q+1</code>, and the
		 * right-hand sides are depth 2. Lastly, <code>q</code> and <code>1</code> in
		 * the last equality are depth 3.
		 * 
		 * On the other hand, given
		 * 
		 * <pre>
		 * ((x == 0) && (y == 1)) || ((z == 0) && (q + 1 == 2))
		 * </pre>
		 * 
		 * the whole expression is depth 1, and <code>((x==0) && (y==1))</code> and
		 * <code>((z==2) && (q+1==3))</code> are both depth 2. Subexpressions have
		 * greater depths, as before.
		 */
		private int depth = 0;

		/**
		 * Return the disjoint-set computed by the visitor.
		 *
		 * @return computed disjoint-set
		 */
		public DisjointSet<Expression> getDisjointSet() {
			return disjointSet;
		}

		/**
		 * Check if the given variable occurs in a disjoint-set. If so, merge that set
		 * with the set of the current proposition and update the {@link #rootMap} for
		 * the variable. Otherwise, update {@link #rootMap} to "place" the variable in
		 * the disjoint-set to which the current proposition belongs.
		 *
		 * @param variable variable to handle
		 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.Variable)
		 */
		@Override
		public void postVisit(Variable variable) {
			Expression proposition = rootMap.get(variable);
			if (proposition == null) {
				rootMap.put(variable, disjointSet.find(currentProposition));
			} else {
				Expression newRoot = disjointSet.union(proposition, currentProposition);
				if (newRoot != proposition) {
					rootMap.put(variable, newRoot);
				}
			}
		}

		/**
		 * Increment the depth if we are not dealing with an "and" operation or if we
		 * have already passed depth 1. If the resulting depth is 1, the current
		 * operation becomes the current proposition and it is added to the disjoint-set
		 * (since this is the first time we encounter it).
		 *
		 * @param operation operation to handle
		 * @see za.ac.sun.cs.green.expr.Visitor#preVisit(za.ac.sun.cs.green.expr.Operation)
		 */
		@Override
		public void preVisit(Operation operation) {
			if ((operation.getOperator() != Operator.AND) || (depth > 0)) {
				depth++;
			}
			if (depth == 1) {
				currentProposition = operation;
				disjointSet.addElement(operation);
			}
		}

		/**
		 * Re-adjust the depth.
		 *
		 * @param operation operation to handle
		 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.Operation)
		 */
		@Override
		public void postVisit(Operation operation) {
			if (depth > 0) {
				depth--;
			}
		}

	}

	// ======================================================================
	//
	// DISJOINT SET IMPLEMENTATION
	//
	// ======================================================================

	/**
	 * Implementation of disjoint-set data structure.
	 * 
	 * @param <T> type of set elements
	 */
	private static class DisjointSet<T> {

		/**
		 * Map each element to its parent element.
		 */
		private final Map<T, T> parentMap = new LinkedHashMap<>();

		/**
		 * Map each element to its rank.
		 */
		private final Map<T, Integer> rankMap = new HashMap<>();

		/**
		 * Return the set of elements.
		 *
		 * @return set of elements
		 */
		public Set<T> getElements() {
			return parentMap.keySet();
		}

		/**
		 * Add a new element to the set of all elements. The new element is put in a
		 * singleton set of its own, and given the rank 0.  If the element is already present, it is ignored.
		 *
		 * @param element new element to add
		 */
		public void addElement(T element) {
			// OLD:
			// if (parentMap.containsKey(element)) {
			// 	throw new IllegalArgumentException("element is already contained in UnionFind: " + element);
			// }
			if (!parentMap.containsKey(element)) {
				parentMap.put(element, element);
				rankMap.put(element, 0);
			}
		}

		/**
		 * Find the root (representative) element of a given element. This
		 * implementation uses Tarjan and Van Leeuwen's "path splitting" mechanism.
		 *
		 * @param element the element to search for
		 * @return representative element
		 */
		public T find(T element) {
			T parent = parentMap.get(element);
			if (parent == null) {
				throw new IllegalArgumentException("element is not contained in this data structure: " + element);
			}
			while (!parent.equals(element)) {
				T prev = element;
				element = parent;
				parent = parentMap.get(element);
				parentMap.put(prev, parent);
			}
			return element;
		}

		/**
		 * Merge the disjoint sets in which the parameters appear and return the
		 * representative for the new, merged set. This implementation uses
		 * union-by-rank.
		 *
		 * @param element1 first element
		 * @param element2 second element
		 * @return representative of the newly-merged set that contains the parameters
		 */
		public T union(T element1, T element2) {
			if (!parentMap.containsKey(element1) || !parentMap.containsKey(element2)) {
				throw new IllegalArgumentException("elements must be contained in given set");
			}
			T parent1 = find(element1);
			T parent2 = find(element2);
			if (parent1.equals(parent2)) {
				return parent1;
			}
			int rank1 = rankMap.get(parent1);
			int rank2 = rankMap.get(parent2);
			if (rank1 < rank2) {
				parentMap.put(parent1, parent2);
				return parent2;
			} else if (rank1 > rank2) {
				parentMap.put(parent2, parent1);
			} else {
				parentMap.put(parent2, parent1);
				rankMap.put(parent1, rank1 + 1);
			}
			return parent1;
		}

	}

}
