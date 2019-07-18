/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.canonizer;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.SortedSet;
import java.util.Stack;
import java.util.TreeMap;
import java.util.TreeSet;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.service.BasicService;
import za.ac.sun.cs.green.util.Reporter;
import za.ac.sun.cs.green.expr.BoolVariable;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Operation.Operator;
import za.ac.sun.cs.green.expr.RealVariable;
import za.ac.sun.cs.green.expr.StringVariable;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;

/**
 * Canonizer service for SAT problems.
 */
public class SATCanonizerService extends BasicService {

	// ======================================================================
	//
	// COUNTERS
	//
	// ======================================================================

	/**
	 * Number of times this service has been invoked.
	 */
	protected int invocationCount = 0;

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
	 * Create a service to canonize expressions for SAT queries.
	 * 
	 * @param solver
	 *               the associated Green solver
	 */
	public SATCanonizerService(Green solver) {
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
		reporter.report("serviceTimeConsumption", serviceTimeConsumption);
	}

	/**
	 * Process an incoming request. This checks if the instance contains satellite
	 * data for the solution, and, if not, canonizes the instance.
	 * 
	 * @param instance
	 *                 problem to solve
	 * @return singleton set with new canonized instance
	 *
	 * @see za.ac.sun.cs.green.service.BasicService#processRequest(za.ac.sun.cs.green.Instance)
	 */
	@SuppressWarnings("unchecked")
	@Override
	public Set<Instance> processRequest(Instance instance) {
		log.trace("[{}]", instance);
		long startTime = System.currentTimeMillis();
		invocationCount++;
		Object result = instance.getData(getClass());
		if (!(result instanceof Set<?>)) {
			final Map<Variable, Variable> map = new HashMap<Variable, Variable>();
			final Expression expression = canonize(instance.getFullExpression(), map);
			final Instance newInstance = new Instance(getSolver(), instance.getSource(), null, expression);
			result = Collections.singleton(newInstance);
			instance.setData(getClass(), result);
		}
		serviceTimeConsumption += (System.currentTimeMillis() - startTime);
		return (Set<Instance>) result;
	}

	/**
	 * Canonize an expression. The steps are:
	 * 
	 * <ol>
	 * <li>reorder equations,</li>
	 * <li>normalize the expression, and</li>
	 * <li>rename the variables.</li>
	 * </ol>
	 * 
	 * @param expression
	 *                   what to canonize
	 * @param map
	 *                   mapping of old to new variable names
	 * @return the canonized expression
	 */
	public Expression canonize(Expression expression, Map<Variable, Variable> map) {
		try {
			log.trace("before: {}", expression);
			OrderingVisitor orderingVisitor = new OrderingVisitor();
			expression.accept(orderingVisitor);
			expression = orderingVisitor.getExpression();
			log.trace("after ordering: {}", expression);
			NormalizationVisitor canonizationVisitor = new NormalizationVisitor();
			expression.accept(canonizationVisitor);
			Expression canonized = canonizationVisitor.getExpression();
			log.trace("after canonization: {}", canonized);
			if (canonized != null) {
				canonized = new RenamerVisitor(map, canonizationVisitor.getVariableSet()).rename(canonized);
				log.trace("after renaming: {}", canonized);
			}
			return canonized;
		} catch (VisitorException x) {
			log.fatal("encountered an exception -- this should not be happening!", x);
		}
		return null;
	}

	// ======================================================================
	//
	// RE-ORDERING VISITOR
	//
	// ======================================================================

	/**
	 * The ordering visitor normalizes expressions of the form "@{code A <> B}",
	 * where "@{code <>}" is one of "{@code ==}", "{@code !=}", "{@code <}",
	 * "{@code <=}", "{@code >}", or "{@code >=}". The operands are swapped:
	 * 
	 * <ul>
	 * <li>If both are variables, they are arranged alphabetically.</li>
	 * <li>If {@code A} is a constant and {@code B} is a variable, they are
	 * swapped.</li>
	 * <li>Otherwise, the operation remains the same.</li>
	 * </ul>
	 * 
	 * If the operands and swapped, the operator is changed appropriately.
	 */
	private static class OrderingVisitor extends Visitor {

		/**
		 * Stack where operands are stored.
		 */
		private Stack<Expression> stack;

		/**
		 * Create an ordering visitor.
		 */
		OrderingVisitor() {
			stack = new Stack<Expression>();
		}

		/**
		 * Return the resulting re-ordered expression.
		 * 
		 * @return re-ordered expression
		 */
		public Expression getExpression() {
			return stack.pop();
		}

		/**
		 * Place constants on the stack.
		 *
		 * @param constant
		 *                 constant to place on the stack
		 *
		 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.Constant)
		 */
		@Override
		public void postVisit(Constant constant) {
			stack.push(constant);
		}

		/**
		 * Place variables on the stack.
		 *
		 * @param variable
		 *                 variable to place on the stack
		 *
		 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.Variable)
		 */
		@Override
		public void postVisit(Variable variable) {
			stack.push(variable);
		}

		/**
		 * Swap the operands of an operation under the conditions outlined in the class
		 * description and place it on the stack.
		 *
		 * @param operation
		 *                  operation to reorder
		 * @throws VisitorException
		 *                          never
		 *
		 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.Operation)
		 */
		@Override
		public void postVisit(Operation operation) throws VisitorException {
			Operation.Operator op = operation.getOperator();
			Operation.Operator newOp = null;
			switch (op) {
			case EQ:
				newOp = Operator.EQ;
				break;
			case NE:
				newOp = Operator.NE;
				break;
			case LT:
				newOp = Operator.GT;
				break;
			case LE:
				newOp = Operator.GE;
				break;
			case GT:
				newOp = Operator.LT;
				break;
			case GE:
				newOp = Operator.LE;
				break;
			default:
				break;
			}
			if (newOp != null) {
				Expression r = stack.pop();
				Expression l = stack.pop();
				if ((r instanceof IntVariable) && (l instanceof IntVariable)
						&& (((IntVariable) r).getName().compareTo(((IntVariable) l).getName()) < 0)) {
					stack.push(new Operation(newOp, r, l));
				} else if ((r instanceof IntVariable) && (l instanceof IntConstant)) {
					stack.push(new Operation(newOp, r, l));
				} else {
					stack.push(operation);
				}
			} else if (op.getArity() == 2) {
				Expression r = stack.pop();
				Expression l = stack.pop();
				stack.push(new Operation(op, l, r));
			} else {
				for (int i = op.getArity(); i > 0; i--) {
					stack.pop();
				}
				stack.push(operation);
			}
		}

	}

	// ======================================================================
	//
	// NORMALIZATION VISITOR
	//
	// ======================================================================

	/**
	 * Visitor to normalize expressions. Constant operations are folded, expressions
	 * are rearranged to group identical variables and their coefficients are added
	 * up, and operations are swapped when necessary.
	 */
	private static class NormalizationVisitor extends Visitor {

		/**
		 * Stack of operands.
		 */
		private final Stack<Expression> stack = new Stack<>();

		/**
		 * Set of final conjuncts.
		 */
		private final SortedSet<Expression> conjuncts = new TreeSet<>();

		/**
		 * Set of variables encountered.
		 */
		private final SortedSet<IntVariable> variableSet = new TreeSet<>();

		/**
		 * Flag that indicates that the expression was found to be unsatisfiable. For
		 * example, the expression "{@code (x > 0) && (2 == 3)}" is trivially
		 * unsatisfiable.
		 */
		private boolean unsatisfiable;

		/**
		 * Flag that indicates that the expression is linear and integer.
		 */
		private boolean linearInteger;

		/**
		 * Create a normalization visitor.
		 */
		NormalizationVisitor() {
			unsatisfiable = false;
			linearInteger = true;
		}

		/**
		 * Return the set of variables encountered.
		 *
		 * @return set of variables in expression
		 */
		public SortedSet<IntVariable> getVariableSet() {
			return variableSet;
		}

		/**
		 * Normalize the expression and return the result.
		 *
		 * @return normalized expression
		 */
		public Expression getExpression() {
			if (!linearInteger) {
				return null;
			} else if (unsatisfiable) {
				return Operation.FALSE;
			} else {
				if (!stack.isEmpty()) {
					Expression x = stack.pop();
					if (x.equals(Operation.FALSE)) {
						return Operation.FALSE;
					} else if (!x.equals(Operation.TRUE)) {
						conjuncts.add(x);
					}
				}
				SortedSet<Expression> newConjuncts = conjuncts;
				Expression c = null;
				for (Expression e : newConjuncts) {
					if (e.equals(Operation.FALSE)) {
						return Operation.FALSE;
					} else if (e instanceof Operation) {
						Operation o = (Operation) e;
						if (o.getOperator() == Operator.GT) {
							e = Operation.lt(scale(-1, o.getOperand(0)), o.getOperand(1));
						} else if (o.getOperator() == Operator.GE) {
							e = Operation.le(scale(-1, o.getOperand(0)), o.getOperand(1));
						}
						o = (Operation) e;
						if (o.getOperator() == Operator.GT) {
							e = Operation.ge(merge(o.getOperand(0), new IntConstant(-1)), o.getOperand(1));
						} else if (o.getOperator() == Operator.LT) {
							e = Operation.le(merge(o.getOperand(0), new IntConstant(1)), o.getOperand(1));
						}
					}
					c = (c == null) ? e : Operation.and(c, e);
				}
				return (c == null) ? Operation.TRUE : c;
			}
		}

		/**
		 * Visit and normalize a constant. If everything is under control and the
		 * constant is an integer, it is placed on the stack. Otherwise, if we are not
		 * dealing with LIA or have found the expression to be unsatisfiable or the
		 * constant is not an integer, the stack is cleared and the LIA flag is set to
		 * false.
		 *
		 * @param constant
		 *                 constant to investigate
		 *
		 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.Constant)
		 */
		@Override
		public void postVisit(Constant constant) {
			if (linearInteger && !unsatisfiable) {
				if (constant instanceof IntConstant) {
					stack.push(constant);
				} else {
					stack.clear();
					linearInteger = false;
				}
			}
		}

		/**
		 * Visit and normalize a variable. If everything is under control and the
		 * variable is an integer, it is placed on the stack. Otherwise, if we are not
		 * dealing with LIA or have found the expression to be unsatisfiable or the
		 * variable is not an integer, the stack is cleared and the LIA flag is set to
		 * false.
		 *
		 * @param variable
		 *                 variable to investigate
		 *
		 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.Variable)
		 */
		@Override
		public void postVisit(Variable variable) {
			if (linearInteger && !unsatisfiable) {
				if (variable instanceof IntVariable) {
					variableSet.add((IntVariable) variable);
					stack.push(Operation.mul(Operation.ONE, variable));
				} else {
					stack.clear();
					linearInteger = false;
				}
			}
		}

		/**
		 * Visit and normalize an operation.
		 *
		 * @param operation
		 *                  operation to investigate
		 * @throws VisitorException
		 *                          never
		 *
		 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.Operation)
		 */
		@Override
		public void postVisit(Operation operation) throws VisitorException {
			if (!linearInteger || unsatisfiable) {
				return;
			}
			Operation.Operator op = operation.getOperator();
			switch (op) {
			case AND:
				if (!stack.isEmpty()) {
					Expression x = stack.pop();
					if (!x.equals(Operation.TRUE)) {
						conjuncts.add(x);
					}
				}
				if (!stack.isEmpty()) {
					Expression x = stack.pop();
					if (!x.equals(Operation.TRUE)) {
						conjuncts.add(x);
					}
				}
				break;
			case EQ:
			case NE:
			case LT:
			case LE:
			case GT:
			case GE:
				if (!stack.isEmpty()) {
					Expression e = merge(scale(-1, stack.pop()), stack.pop());
					if (e instanceof IntConstant) {
						int v = ((IntConstant) e).getValue();
						boolean b = true;
						if (op == Operator.EQ) {
							b = v == 0;
						} else if (op == Operator.NE) {
							b = v != 0;
						} else if (op == Operator.LT) {
							b = v < 0;
						} else if (op == Operator.LE) {
							b = v <= 0;
						} else if (op == Operator.GT) {
							b = v > 0;
						} else if (op == Operator.GE) {
							b = v >= 0;
						}
						if (b) {
							stack.push(Operation.TRUE);
						} else {
							stack.push(Operation.FALSE);
						}
					} else {
						stack.push(new Operation(op, e, Operation.ZERO));
					}
				}
				break;
			case ADD:
				stack.push(merge(stack.pop(), stack.pop()));
				break;
			case SUB:
				stack.push(merge(scale(-1, stack.pop()), stack.pop()));
				break;
			case MUL:
				if (stack.size() >= 2) {
					Expression r = stack.pop();
					Expression l = stack.pop();
					if ((l instanceof IntConstant) && (r instanceof IntConstant)) {
						int li = ((IntConstant) l).getValue();
						int ri = ((IntConstant) r).getValue();
						stack.push(new IntConstant(li * ri));
					} else if (l instanceof IntConstant) {
						int li = ((IntConstant) l).getValue();
						stack.push(scale(li, r));
					} else if (r instanceof IntConstant) {
						int ri = ((IntConstant) r).getValue();
						stack.push(scale(ri, l));
					} else {
						stack.clear();
						linearInteger = false;
					}
				}
				break;
			case NOT:
				if (!stack.isEmpty()) {
					Expression e = stack.pop();
					if (e.equals(Operation.TRUE)) {
						e = Operation.FALSE;
					} else if (e.equals(Operation.FALSE)) {
						e = Operation.TRUE;
					} else if (e instanceof Operation) {
						Operation o = (Operation) e;
						switch (o.getOperator()) {
						case NOT:
							e = o.getOperand(0);
							break;
						case EQ:
							e = Operation.ne(o.getOperand(0), o.getOperand(1));
							break;
						case NE:
							e = Operation.eq(o.getOperand(0), o.getOperand(1));
							break;
						case GE:
							e = Operation.lt(o.getOperand(0), o.getOperand(1));
							break;
						case GT:
							e = Operation.le(o.getOperand(0), o.getOperand(1));
							break;
						case LE:
							e = Operation.gt(o.getOperand(0), o.getOperand(1));
							break;
						case LT:
							e = Operation.ge(o.getOperand(0), o.getOperand(1));
							break;
						default:
							break;
						}
					}
					stack.push(e);
				}
				break;
			default:
				break;
			}
		}

		/**
		 * Combine two expressions by grouping constants and the coefficients of
		 * identical variables. In essence, the result of {@code merge(A, B)} is
		 * {@code A + B} but similar terms are grouped.
		 *
		 * @param left
		 *              first expression to combine
		 * @param right
		 *              second expression to combine
		 * @return combined expression
		 */
		private Expression merge(Expression left, Expression right) {
			Operation l = null;
			Operation r = null;
			int s = 0;
			if (left instanceof IntConstant) {
				s = ((IntConstant) left).getValue();
			} else if (hasRightConstant(left)) {
				s = getRightConstant(left);
				l = getLeftOperation(left);
			} else {
				l = (Operation) left;
			}
			if (right instanceof IntConstant) {
				s += ((IntConstant) right).getValue();
			} else if (hasRightConstant(right)) {
				s += getRightConstant(right);
				r = getLeftOperation(right);
			} else {
				r = (Operation) right;
			}
			SortedMap<Variable, Integer> coefficients = new TreeMap<Variable, Integer>();
			IntConstant c;
			Variable v;
			Integer k;

			// Collect the coefficients of l
			if (l != null) {
				while (l.getOperator() == Operator.ADD) {
					Operation o = (Operation) l.getOperand(1);
					assert (o.getOperator() == Operator.MUL);
					c = (IntConstant) o.getOperand(0);
					v = (Variable) o.getOperand(1);
					coefficients.put(v, c.getValue());
					l = (Operation) l.getOperand(0);
				}
				assert (l.getOperator() == Operator.MUL);
				c = (IntConstant) l.getOperand(0);
				v = (Variable) l.getOperand(1);
				coefficients.put(v, c.getValue());
			}

			// Collect the coefficients of r
			if (r != null) {
				while (r.getOperator() == Operator.ADD) {
					Operation o = (Operation) r.getOperand(1);
					assert (o.getOperator() == Operator.MUL);
					c = (IntConstant) o.getOperand(0);
					v = (IntVariable) o.getOperand(1);
					k = coefficients.get(v);
					if (k == null) {
						coefficients.put(v, c.getValue());
					} else {
						coefficients.put(v, c.getValue() + k);
					}
					r = (Operation) r.getOperand(0);
				}
				assert (r.getOperator() == Operator.MUL);
				c = (IntConstant) r.getOperand(0);
				v = (IntVariable) r.getOperand(1);
				k = coefficients.get(v);
				if (k == null) {
					coefficients.put(v, c.getValue());
				} else {
					coefficients.put(v, c.getValue() + k);
				}
			}

			Expression lr = null;
			for (Map.Entry<Variable, Integer> e : coefficients.entrySet()) {
				int coef = e.getValue();
				if (coef != 0) {
					Operation term = Operation.mul(new IntConstant(coef), e.getKey());
					if (lr == null) {
						lr = term;
					} else {
						lr = Operation.add(lr, term);
					}
				}
			}
			if ((lr == null) || (lr instanceof IntConstant)) {
				return new IntConstant((int) s);
			} else if (lr instanceof IntConstant) {
				return new IntConstant(s);
			} else if (s == 0) {
				return lr;
			} else {
				return Operation.add(lr, new IntConstant(s));
			}
		}

		/**
		 * Check if the expression is an operation of the form "{@code A + B}", where
		 * "{@code B}" is an integer constant.
		 *
		 * @param expression
		 *                   expression to examine
		 * @return {@code true} if and only if the expression has the form above
		 */
		private boolean hasRightConstant(Expression expression) {
			return isAddition(expression) && (getRightExpression(expression) instanceof IntConstant);
		}

		/**
		 * Return the right-hand side of a binary operation as an integer constant. We
		 * assume that the expression parameter is an operation.
		 *
		 * @param expression
		 *                   operation to extract RHS of
		 * @return constant on RHS of operation, or 0
		 */
		private int getRightConstant(Expression expression) {
			Expression e = getRightExpression(expression);
			if (e instanceof IntConstant) {
				return ((IntConstant) e).getValue();
			} else {
				return 0;
			}
		}

		/**
		 * Return the left-hand side of a binary operation. We assume that the
		 * expression parameter is an operation.
		 *
		 * @param expression
		 *                   operation to extract LHS of
		 * @return LHS of operation
		 */
		private Expression getLeftExpression(Expression expression) {
			return ((Operation) expression).getOperand(0);
		}

		/**
		 * Return the right-hand side of a binary operation. We assume that the
		 * expression parameter is an operation.
		 *
		 * @param expression
		 *                   operation to extract RHS of
		 * @return RHS of operation
		 */
		private Expression getRightExpression(Expression expression) {
			return ((Operation) expression).getOperand(1);
		}

		/**
		 * Return the left-hand side of a binary operation as an operation. We assume
		 * that the expression parameter is an operation.
		 *
		 * @param expression
		 *                   operation to extract LHS of
		 * @return LHS operation of operation
		 */
		private Operation getLeftOperation(Expression expression) {
			return (Operation) getLeftExpression(expression);
		}

		/**
		 * Check if an operation is an addition.
		 *
		 * @param expression
		 *                   operation to investigate
		 * @return {@code true} if and only if the expression is an operation with an
		 *         addition operator
		 */
		private boolean isAddition(Expression expression) {
			return ((Operation) expression).getOperator() == Operator.ADD;
		}

		/**
		 * Scale all the constants in an expression.
		 *
		 * @param factor
		 *                   scaling factor
		 * @param expression
		 *                   expression to scale
		 * @return scaled expression
		 */
		private Expression scale(int factor, Expression expression) {
			if (factor == 0) {
				return Operation.ZERO;
			}
			if (expression instanceof IntConstant) {
				return new IntConstant(factor * ((IntConstant) expression).getValue());
			} else if (expression instanceof IntVariable) {
				return expression;
			} else {
				assert (expression instanceof Operation);
				Operation o = (Operation) expression;
				Operation.Operator p = o.getOperator();
				Expression l = scale(factor, o.getOperand(0));
				Expression r = scale(factor, o.getOperand(1));
				return new Operation(p, l, r);
			}
		}

	}

	// ======================================================================
	//
	// RENAMING VISITOR
	//
	// ======================================================================

	/**
	 * Visitor to rename variables canonically.
	 */
	private static class RenamerVisitor extends Visitor {

		/**
		 * Map from old variables to new variables.
		 */
		private Map<Variable, Variable> map;

		/**
		 * Stack of operands.
		 */
		private Stack<Expression> stack;

		/**
		 * Create a renaming visitor that will populate the given variable map and
		 * renaming variables. The second parameter is ignored.
		 * 
		 * @param map
		 *                    variable map to populate
		 * @param variableSet
		 *                    sorted set of variables
		 */
		RenamerVisitor(Map<Variable, Variable> map, SortedSet<IntVariable> variableSet) {
			this.map = map;
			stack = new Stack<Expression>();
		}

		/**
		 * Rename the variables of the given expression.
		 *
		 * @param expression
		 *                   expression whose variables to rename
		 * @return new expression with renamed variables
		 * @throws VisitorException
		 *                          never
		 */
		public Expression rename(Expression expression) throws VisitorException {
			expression.accept(this);
			return stack.pop();
		}

		/**
		 * Rename a variable by placing a new renamed version on the stack.
		 *
		 * @param variable
		 *                 old variable
		 *
		 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.IntVariable)
		 */
		@Override
		public void postVisit(Variable variable) {
			Variable v = map.get(variable);
			if (v == null) {
				if (variable instanceof BoolVariable) {
					v = new BoolVariable("b" + map.size());
				} else if (variable instanceof IntVariable) {
					IntVariable i = (IntVariable) variable;
					v = new IntVariable("v" + map.size(), i.getLowerBound(), i.getUpperBound());
				} else if (variable instanceof RealVariable) {
					RealVariable r = (RealVariable) variable;
					v = new RealVariable("r" + map.size(), r.getLowerBound(), r.getUpperBound());
				} else if (variable instanceof StringVariable) {
					v = new StringVariable("s" + map.size());
				} else {
					v = variable;
				}
				map.put(variable, v);
			}
			stack.push(v);
		}

		/**
		 * Place a constant on the stack.
		 *
		 * @param constant
		 *                 constant to place on the stack
		 *
		 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.Constant)
		 */
		@Override
		public void postVisit(Constant constant) {
			stack.push(constant);
		}

		/**
		 * Rename an operation by removing the renamed operands and placing a new
		 * operation on the stack.
		 *
		 * @param operation
		 *                  operation to rename
		 *
		 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.Operation)
		 */
		@Override
		public void postVisit(Operation operation) {
			int arity = operation.getOperator().getArity();
			Expression[] operands = new Expression[arity];
			for (int i = arity; i > 0; i--) {
				if (stack.isEmpty()) {
					System.out.println("SOMETHING");
				}
				operands[i - 1] = stack.pop();
			}
			stack.push(new Operation(operation.getOperator(), operands));
		}

	}

}
