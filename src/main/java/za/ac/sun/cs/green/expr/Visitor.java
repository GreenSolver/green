/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.expr;

/**
 * Abstract base class for visitors over GREEN expressions. This class contains
 * two routines ("{@code preVisit(X)}" and "{@code postVisit(X)}") for each
 * expression class "{@code X}". This allows subclasses to be very specific
 * about how to handle pre- and post-visits to expressions.
 */
public abstract class Visitor {

	// ======================================================================
	//
	// PRE VISITS
	//
	// ======================================================================

	/**
	 * Pre-visit a boolean variable.
	 *
	 * @param boolVariable
	 *                   variable to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void preVisit(BoolVariable boolVariable) throws VisitorException {
		preVisit((Variable) boolVariable);
	}

	/**
	 * Pre-visit a constant expression.
	 *
	 * @param constant
	 *                 constant to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void preVisit(Constant constant) throws VisitorException {
		preVisit((Expression) constant);
	}

	/**
	 * Pre-visit a general expression.
	 *
	 * @param expression
	 *                   expression to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void preVisit(Expression expression) throws VisitorException {
	}

	/**
	 * Pre-visit an integer constant.
	 *
	 * @param intConstant
	 *                   constant to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void preVisit(IntConstant intConstant) throws VisitorException {
		preVisit((Constant) intConstant);
	}

	/**
	 * Pre-visit an integer variable.
	 *
	 * @param intVariable
	 *                   variable to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void preVisit(IntVariable intVariable) throws VisitorException {
		preVisit((Variable) intVariable);
	}

	/**
	 * Pre-visit an operation.
	 *
	 * @param operation
	 *                   operation to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void preVisit(Operation operation) throws VisitorException {
		preVisit((Expression) operation);
	}

	/**
	 * Pre-visit a real constant.
	 *
	 * @param realConstant
	 *                   constant to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void preVisit(RealConstant realConstant) throws VisitorException {
		preVisit((Constant) realConstant);
	}

	/**
	 * Pre-visit a real variable.
	 *
	 * @param realVariable
	 *                   variable to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void preVisit(RealVariable realVariable) throws VisitorException {
		preVisit((Variable) realVariable);
	}

	/**
	 * Pre-visit a string constant.
	 *
	 * @param stringConstant
	 *                   constant to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void preVisit(StringConstant stringConstant) throws VisitorException {
		preVisit((Constant) stringConstant);
	}

	/**
	 * Pre-visit a string variable.
	 *
	 * @param stringVariable
	 *                   variable to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void preVisit(StringVariable stringVariable) throws VisitorException {
		preVisit((Variable) stringVariable);
	}

	/**
	 * Pre-visit a variable.
	 *
	 * @param variable
	 *                   variable to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void preVisit(Variable variable) throws VisitorException {
		preVisit((Expression) variable);
	}

	// ======================================================================
	//
	// POST VISITS
	//
	// ======================================================================

	/**
	 * Post-visit a boolean variable.
	 *
	 * @param boolVariable
	 *                   variable to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void postVisit(BoolVariable boolVariable) throws VisitorException {
		postVisit((Variable) boolVariable);
	}

	/**
	 * Post-visit a constant expression.
	 *
	 * @param constant
	 *                 expression to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void postVisit(Constant constant) throws VisitorException {
		postVisit((Expression) constant);
	}

	/**
	 * Post-visit a general expression.
	 *
	 * @param expression
	 *                   expression to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void postVisit(Expression expression) throws VisitorException {
	}

	/**
	 * Post-visit an integer constant.
	 *
	 * @param intConstant
	 *                   constant to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void postVisit(IntConstant intConstant) throws VisitorException {
		postVisit((Constant) intConstant);
	}

	/**
	 * Post-visit an integer variable.
	 *
	 * @param intVariable
	 *                   variable to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void postVisit(IntVariable intVariable) throws VisitorException {
		postVisit((Variable) intVariable);
	}

	/**
	 * Post-visit an operation.
	 *
	 * @param operation
	 *                   operation to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void postVisit(Operation operation) throws VisitorException {
		postVisit((Expression) operation);
	}

	/**
	 * Post-visit a real constant.
	 *
	 * @param realConstant
	 *                   constant to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void postVisit(RealConstant realConstant) throws VisitorException {
		postVisit((Constant) realConstant);
	}

	/**
	 * Post-visit a real variable.
	 *
	 * @param realVariable
	 *                   variable to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void postVisit(RealVariable realVariable) throws VisitorException {
		postVisit((Variable) realVariable);
	}

	/**
	 * Post-visit a string constant.
	 *
	 * @param stringConstant
	 *                   constant to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void postVisit(StringConstant stringConstant) throws VisitorException {
		postVisit((Constant) stringConstant);
	}

	/**
	 * Post-visit a string variable.
	 *
	 * @param stringVariable
	 *                   variable to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void postVisit(StringVariable stringVariable) throws VisitorException {
		postVisit((Variable) stringVariable);
	}

	/**
	 * Post-visit a variable.
	 *
	 * @param variable
	 *                   variable to visit
	 * @throws VisitorException
	 *                          passed on from the visitor
	 */
	public void postVisit(Variable variable) throws VisitorException {
		postVisit((Expression) variable);
	}

}
