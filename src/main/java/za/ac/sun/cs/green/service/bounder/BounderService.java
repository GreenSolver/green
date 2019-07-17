/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.bounder;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.RealConstant;
import za.ac.sun.cs.green.expr.RealVariable;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.service.BasicService;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Associate bounds with variables.
 * 
 * It is often desirable to explicitly add variable bounds to an expression. For
 * example, "x==y" could become "(x==y)&(x>0)&(x<10)&(y>0)&(y<10)". This is
 * necessary in many cases where variables with different bounds occur within a
 * program, or where the user wants to count the number of solutions.
 * 
 * This service collects the bounds for all the variables that occur within the
 * expression associated with a given instance. The bounds are expressed as a
 * conjunction and added (in a new instance) to the parent instance of the input
 * instance. It is added to the parent because we do not want to influence any
 * slicing tools. And it is added to a new instance, so that the original
 * instance is not distorted in any way.
 */
public class BounderService extends BasicService {

	// ======================================================================
	//
	// COUNTERS
	//
	// ======================================================================

	/**
	 * Number of times this service has been invoked.
	 */
	protected int invocationCount = 0;

	/**
	 * Total number of variables processed.
	 */
	protected int totalVariableCount = 0;

	// ======================================================================
	//
	// TIME CONSUMPTION
	//
	// ======================================================================

	/**
	 * Milliseconds spent to process requests.
	 */
	protected long serviceTimeConsumption = 0;

	// ======================================================================
	//
	// CONSTRUCTOR & METHODS
	//
	// ======================================================================

	/**
	 * Construct an instance of the bounder service.
	 *
	 * @param solver
	 *               associated Green solver
	 */
	public BounderService(Green solver) {
		super(solver);
	}

	/**
	 * Report the statistics gathered.
	 *
	 * @param reporter
	 *                 the mechanism through which reporting is done
	 *
	 * @see za.ac.sun.cs.green.service.BasicService#report(za.ac.sun.cs.green.util.Reporter)
	 */
	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("invocationCount", invocationCount);
		reporter.report("totalVariableCount", totalVariableCount);
		reporter.report("serviceTimeConsumption", serviceTimeConsumption);
	}

	/**
	 * Process an incoming request. This checks if the instance contains satellite
	 * data for the solution, and, if not, solves the instance itself. This amounts
	 * to adding the bounds as expressions to a new instance of the incoming
	 * problem.
	 * 
	 * @param instance
	 *                 problem to solve
	 * @return singleton set with new bounded instance
	 *
	 * @see za.ac.sun.cs.green.service.BasicService#processRequest(za.ac.sun.cs.green.Instance)
	 */
	@SuppressWarnings("unchecked")
	@Override
	public Set<Instance> processRequest(Instance instance) {
		long start = System.currentTimeMillis();
		invocationCount++;
		Object result = instance.getData(getClass());
		if (!(result instanceof Set<?>)) {
			Expression boundedExpression = bound(instance.getFullExpression());
			final Instance parent = instance.getParent();
			if (parent != null) {
				boundedExpression = Operation.and(parent.getFullExpression(), boundedExpression);
			}
			final Instance q = new Instance(getSolver(), instance.getSource(), null, boundedExpression);
			final Instance i = new Instance(getSolver(), instance.getSource(), q, instance.getExpression());
			result = Collections.singleton(i);
			instance.setData(getClass(), result);
		}
		serviceTimeConsumption += (System.currentTimeMillis() - start);
		return (Set<Instance>) result;
	}

	/**
	 * Collect all of the variables that appear in an expression and construct
	 * conjuncts that encode the minimum and maximum bounds on the variables. Then
	 * return a new expression which consists of the conjunction of the bounds.
	 * 
	 * @param expression
	 *                   the input expression
	 * @return bound conjuncts for all of the variables in the input
	 */
	private Expression bound(Expression expression) {
		Expression newExpression = null;
		try {
			Set<Variable> variables = new VariableCollectorVisitor().getVariables(expression);
			totalVariableCount += variables.size();
			for (Variable variable : variables) {
				if (variable instanceof IntVariable) {
					IntVariable i = (IntVariable) variable;
					Operation lower = Operation.ge(i, new IntConstant(i.getLowerBound()));
					Operation upper = Operation.le(i, new IntConstant(i.getUpperBound()));
					Operation bound = Operation.and(lower, upper);
					if (newExpression == null) {
						newExpression = bound;
					} else {
						newExpression = Operation.and(newExpression, bound);
					}
				} else if (variable instanceof RealVariable) {
					RealVariable r = (RealVariable) variable;
					Operation lower = Operation.ge(r, new RealConstant(r.getLowerBound()));
					Operation upper = Operation.le(r, new RealConstant(r.getUpperBound()));
					Operation bound = Operation.and(lower, upper);
					if (newExpression == null) {
						newExpression = bound;
					} else {
						newExpression = Operation.and(newExpression, bound);
					}
				} else {
					log.warn("NOT adding bounds for variable \"{}\"", variable.getName());
				}
			}
		} catch (VisitorException x) {
			log.fatal("encountered an exception -- this should not be happening!", x);
		}
		return (newExpression == null) ? Operation.TRUE : newExpression;
	}

	// ======================================================================
	//
	// COLLECT VARIABLES IN EXPRESSION
	//
	// ======================================================================

	/**
	 * Visitor that traverses an expression, collecting variables.
	 */
	private static class VariableCollectorVisitor extends Visitor {

		/**
		 * Variables encountered in expression.
		 */
		private final Set<Variable> variables;

		/**
		 * Create a variable collector visitor.
		 */
		VariableCollectorVisitor() {
			variables = new HashSet<Variable>();
		}

		/**
		 * Return the variables inside an expression.
		 *
		 * @param expression expression to traverse over
		 * @return the set of variables
		 * @throws VisitorException never
		 */
		public Set<Variable> getVariables(Expression expression) throws VisitorException {
			variables.clear();
			expression.accept(this);
			return variables;
		}

		/**
		 * Add variable to set.
		 *
		 * @param variable variable encountered
		 *
		 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.Variable)
		 */
		@Override
		public void postVisit(Variable variable) {
			variables.add(variable);
		}

	}

}
