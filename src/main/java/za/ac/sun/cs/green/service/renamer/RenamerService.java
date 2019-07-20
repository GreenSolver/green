/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.renamer;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.service.BasicService;
import za.ac.sun.cs.green.util.Reporter;

/**
 * A service that renames the variables of an expression.
 */
public class RenamerService extends BasicService {

	/**
	 * Number of times the renamer has been invoked.
	 */
	private int invocationCount = 0;

	/**
	 * Milliseconds spent executing the service
	 */
	private long timeConsumption = 0;

	/**
	 * Create a renamer service.
	 * 
	 * @param solver
	 *               associated GREEN solver
	 */
	public RenamerService(Green solver) {
		super(solver);
	}

	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("invocationCount", invocationCount);
		reporter.report("timeConsumption", timeConsumption);
	}

	@Override
	public Set<Instance> processRequest(Instance instance) {
		long startTime = System.currentTimeMillis();
		invocationCount++;
		@SuppressWarnings("unchecked")
		Set<Instance> result = (Set<Instance>) instance.getData(getClass());
		if (result == null) {
			final Map<Variable, Variable> map = new HashMap<Variable, Variable>();
			final Expression expression = rename(instance.getFullExpression(), map);
			final Instance newInstance = new Instance(getSolver(), instance.getSource(), null, expression);
			result = Collections.singleton(newInstance);
			instance.setData(getClass(), result);
		}
		timeConsumption += System.currentTimeMillis() - startTime;
		return result;
	}

	/**
	 * Rename the variables of an expression and populating the given map with a
	 * mapping from old variables to new variables.
	 *
	 * @param expression
	 *                   expression to rename
	 * @param map
	 *                   variable mapping to populate
	 * @return renamed expression
	 */
	private Expression rename(Expression expression, Map<Variable, Variable> map) {
		try {
			log.debug("before tenaming: {}", () -> expression);
			Expression renamed = new Renamer(map).rename(expression);
			log.debug("after renaming: {}", () -> renamed);
			return renamed;
		} catch (VisitorException x) {
			log.fatal("encountered an exception -- this should not be happening!", x);
		}
		return null;
	}

	// ======================================================================
	//
	// VISITOR THAT RENAMES VARIABLES
	//
	// ======================================================================

	/**
	 * Visitor that renames variables.
	 */
	private static class Renamer extends Visitor {

		/**
		 * Mapping from old to new variables.
		 */
		private final Map<Variable, Variable> map;

		/**
		 * Stack of operands.
		 */
		private final Stack<Expression> stack = new Stack<Expression>();

		/**
		 * Create a new renaming visitor.
		 * 
		 * @param map
		 *            variable mapping to populate
		 */
		Renamer(final Map<Variable, Variable> map) {
			this.map = map;
		}

		/**
		 * Rename the variables of the given expression.
		 *
		 * @param expression
		 *                   expression to rename
		 * @return renamed expression
		 * @throws VisitorException
		 *                          should never happen
		 */
		public Expression rename(Expression expression) throws VisitorException {
			expression.accept(this);
			return stack.pop();
		}

		/**
		 * Handle a variable by adding it to the map (if not already present) and
		 * placing the new, renamed variable on the stack.
		 *
		 * @param variable
		 *                 variable to process
		 *
		 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.IntVariable)
		 */
		@Override
		public void postVisit(IntVariable variable) {
			Variable v = map.get(variable);
			if (v == null) {
				v = new IntVariable("v" + map.size(), variable.getLowerBound(), variable.getUpperBound());
				map.put(variable, v);
			}
			stack.push(v);
		}

		/**
		 * Handle a constant by placing it on the stack.
		 *
		 * @param constant
		 *                 constant to process
		 *
		 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.Constant)
		 */
		@Override
		public void postVisit(Constant constant) {
			stack.push(constant);
		}

		/**
		 * Handle an operation by removing its operands from the stack and placing a new
		 * (renamed) operation on the stack.
		 *
		 * @param operation
		 *                  operation to process
		 *
		 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.Operation)
		 */
		@Override
		public void postVisit(Operation operation) {
			int arity = operation.getOperator().getArity();
			Expression[] operands = new Expression[arity];
			for (int i = arity; i > 0; i--) {
				operands[i - 1] = stack.pop();
			}
			stack.push(new Operation(operation.getOperator(), operands));
		}

	}

}
