/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.choco4;

import java.util.Map;
import java.util.Stack;
import java.util.function.BiFunction;

import org.apache.logging.log4j.Logger;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.expression.discrete.arithmetic.ArExpression;
import org.chocosolver.solver.expression.discrete.relational.ReExpression;
import org.chocosolver.solver.variables.IntVar;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;

/**
 * Translator for a GREEN instance to Choco4 representation.
 */
public class ChocoTranslator extends Visitor {

	/**
	 * The Java {@link Logger} associated with the {@link Green} solver.
	 */
	protected final Logger log;

	/**
	 * Handle for the Choco4 system.
	 */
	private final Model chocoModel;

	/**
	 * Mapping from GREEN variables to Choco4 variables.
	 */
	private final Map<Variable, IntVar> variableMap;

	/**
	 * Placeholder object. In this implementation, terms (that is, expressions that
	 * are not conjuncts) are placed on the stack, but clauses (that is, expression
	 * that are conjuncts) are registered with the Choco4 model, and this
	 * placeholder is placed on the stack in their place.
	 */
	private final Object placeholder = new Object();

	/**
	 * Stack of operands.
	 */
	private final Stack<Object> stack = new Stack<Object>();

	/**
	 * Create an instance of the Choco4 translator.
	 * 
	 * @param log
	 *                    logging mechanism
	 * @param chocoModel
	 *                    handle for the Choco4 system
	 * @param variableMap
	 *                    mapping from GREEN to Choco4 variables
	 */
	public ChocoTranslator(final Logger log, final Model chocoModel, final Map<Variable, IntVar> variableMap) {
		this.log = log;
		this.chocoModel = chocoModel;
		this.variableMap = variableMap;
	}

	/**
	 * Translate the given expression.
	 *
	 * @param expression
	 *                   expression to translate
	 * @throws VisitorException
	 *                          when an unsupported situation is encountered
	 */
	public void translate(Expression expression) throws VisitorException {
		expression.accept(this);
		assert (stack.isEmpty() || (stack.pop() == placeholder));
	}

	/**
	 * Handle a constant by placing its Java value on the stack.
	 *
	 * @param constant
	 *                 constant to process
	 *
	 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.IntConstant)
	 */
	@Override
	public void postVisit(IntConstant constant) {
		stack.push(constant.getValue());
	}

	/**
	 * Handle an integer variable by creating and recording a corresponding Choco4
	 * variable and placing it on the stack.
	 *
	 * @param variable
	 *                 integer variable to process
	 *
	 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.IntVariable)
	 */
	@Override
	public void postVisit(IntVariable variable) {
		IntVar v = variableMap.get(variable);
		if (v == null) {
			Integer lower = variable.getLowerBound();
			Integer upper = variable.getUpperBound();
			v = chocoModel.intVar(variable.getName(), lower, upper);
			variableMap.put(variable, v);
		}
		stack.push(v);
	}

	/**
	 * Construct a conjunct and register it with the Choco4 model. While the caller
	 * supplies the operands explicitly, the operator (one of {@code ==},
	 * {@code !=}, {@code <}, {@code <=}, {@code >}, {@code >=}) is given as four
	 * binary functions. The choice of function depends on whether the operands are
	 * Java constants or Choco4 expressions.
	 *
	 * @param left
	 *              first operand
	 * @param right
	 *              second operand
	 * @param va
	 *              binary function for Java constant, Java constant
	 * @param vj
	 *              binary function for Choco4 expression, Java constant
	 * @param vi
	 *              binary function for Java constant, Choco4 expression
	 * @param vv
	 *              binary function for Choco4 expression, Choco4 expression
	 */
	private void clause(Object left, Object right, BiFunction<Integer, Integer, Boolean> va,
			BiFunction<ArExpression, Integer, ReExpression> vj, BiFunction<ArExpression, Integer, ReExpression> vi,
			BiFunction<ArExpression, ArExpression, ReExpression> vv) {
		if ((left instanceof Integer) && (right instanceof Integer)) {
			Boolean r = va.apply((Integer) left, (Integer) right);
			(r ? chocoModel.trueConstraint() : chocoModel.falseConstraint()).post();
			log.debug("post: " + r);
		} else if ((left instanceof ArExpression) && (right instanceof Integer)) {
			ReExpression r = vi.apply((ArExpression) left, (Integer) right);
			r.post();
			log.debug("post: " + r);
		} else if ((left instanceof Integer) && (right instanceof ArExpression)) {
			ReExpression r = vj.apply((ArExpression) right, (Integer) left);
			r.post();
			log.debug("post: " + r);
		} else if ((left instanceof ArExpression) && (right instanceof ArExpression)) {
			ReExpression r = vv.apply((ArExpression) left, (ArExpression) right);
			r.post();
			log.debug("post: " + r);
		} else {
			log.fatal("unhandled case (1) left={}, right={}", left, right);
		}
		stack.push(placeholder);
	}

	/**
	 * Shortcut method that saves on (long-ish) binary function parameter. The is
	 * appropriate for symmetric operators (that is {@code ==} or {@code !=}).
	 *
	 * @param left
	 *              first operand
	 * @param right
	 *              second operand
	 * @param va
	 *              binary function for two Java constants
	 * @param vi
	 *              binary function for Java constant, Choco4 expression, order
	 *              unimportant
	 * @param vv
	 *              binary function for two Choco4 expressions
	 */
	private void clause(Object left, Object right, BiFunction<Integer, Integer, Boolean> va,
			BiFunction<ArExpression, Integer, ReExpression> vi,
			BiFunction<ArExpression, ArExpression, ReExpression> vv) {
		clause(left, right, va, vi, vi, vv);
	}

	/**
	 * Construct a Choco4 expression and place it on the stack. While the caller
	 * supplies the operands explicitly, the operator is given as four
	 * binary functions. The choice of function depends on whether the operands are
	 * Java constants or Choco4 expressions.
	 *
	 * @param left
	 *              first operand
	 * @param right
	 *              second operand
	 * @param va
	 *              binary function for Java constant, Java constant
	 * @param vj
	 *              binary function for Choco4 expression, Java constant
	 * @param vi
	 *              binary function for Java constant, Choco4 expression
	 * @param vv
	 *              binary function for Choco4 expression, Choco4 expression
	 */
	private void term(Object left, Object right, BiFunction<Integer, Integer, Integer> va,
			BiFunction<ArExpression, Integer, ArExpression> vj,
			BiFunction<ArExpression, Integer, ArExpression> vi,
			BiFunction<ArExpression, ArExpression, ArExpression> vv) {
		if ((left instanceof Integer) && (right instanceof Integer)) {
			stack.push(va.apply((Integer) left, (Integer) right));
		} else if ((left instanceof ArExpression) && (right instanceof Integer)) {
			stack.push(vj.apply((ArExpression) left, (Integer) right));
		} else if ((left instanceof Integer) && (right instanceof ArExpression)) {
			stack.push(vi.apply((ArExpression) right, (Integer) left));
		} else if ((left instanceof ArExpression) && (right instanceof ArExpression)) {
			stack.push(vv.apply((ArExpression) left, (ArExpression) right));
		} else {
			log.fatal("unhandled case (2) left={}, right={}", left, right);
		}
	}

	/**
	 * Shortcut method that saves on (long-ish) binary function parameter. The is
	 * appropriate for symmetric operators.
	 *
	 * @param left
	 *              first operand
	 * @param right
	 *              second operand
	 * @param va
	 *              binary function for two Java constants
	 * @param vi
	 *              binary function for Java constant, Choco4 expression, order
	 *              unimportant
	 * @param vv
	 *              binary function for two Choco4 expressions
	 */
	private void term(Object left, Object right, BiFunction<Integer, Integer, Integer> va,
			BiFunction<ArExpression, Integer, ArExpression> vi,
			BiFunction<ArExpression, ArExpression, ArExpression> vv) {
		term(left, right, va, vi, vi, vv);
	}
	
	/**
	 * Handle a GREEN operation.
	 *
	 * @param operation operation to process
	 * @throws TranslatorUnsupportedOperation when an operation is not supported
	 *
	 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.Operation)
	 */
	@Override
	public void postVisit(Operation operation) throws TranslatorUnsupportedOperation {
		Object l = null;
		Object r = null;
		int arity = operation.getOperator().getArity();
		if (arity == 2) {
			if (!stack.isEmpty()) {
				r = stack.pop();
			}
			if (!stack.isEmpty()) {
				l = stack.pop();
			}
		} else if (arity == 1) {
			if (!stack.isEmpty()) {
				l = stack.pop();
			}
		}
		switch (operation.getOperator()) {
		case EQ:
			clause(l, r, (a, b) -> a == b, (a, b) -> a.eq(b), (a, b) -> a.eq(b));
			break;
		case NE:
			clause(l, r, (a, b) -> a != b, (a, b) -> a.ne(b), (a, b) -> a.ne(b));
			break;
		case LT:
			clause(l, r, (a, b) -> a < b, (a, b) -> a.gt(b), (a, b) -> a.lt(b), (a, b) -> a.lt(b));
			break;
		case LE:
			clause(l, r, (a, b) -> a <= b, (a, b) -> a.ge(b), (a, b) -> a.le(b), (a, b) -> a.le(b));
			break;
		case GT:
			clause(l, r, (a, b) -> a > b, (a, b) -> a.lt(b), (a, b) -> a.gt(b), (a, b) -> a.gt(b));
			break;
		case GE:
			clause(l, r, (a, b) -> a >= b, (a, b) -> a.le(b), (a, b) -> a.ge(b), (a, b) -> a.ge(b));
			break;
		case AND:
			if (l != null) {
				assert (l == placeholder);
			}
			if (r != null) {
				assert (r == placeholder);
			}
			break;
		case ADD:
			term(l, r, (a, b) -> a + b, (a, b) -> a.add(b), (a, b) -> a.add(b));
			break;
		case SUB:
			term(l, r, (a, b) -> a - b, (a, b) -> a.sub(b), (a, b) -> a.sub(b).neg(), (a, b) -> a.sub(b));
			break;
		case MUL:
			term(l, r, (a, b) -> a * b, (a, b) -> a.mul(b), (a, b) -> a.mul(b));
			break;
		default:
			throw new TranslatorUnsupportedOperation("unsupported operation " + operation.getOperator());
		}
	}

}
