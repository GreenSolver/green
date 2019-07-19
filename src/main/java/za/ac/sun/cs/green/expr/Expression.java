/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.expr;

import java.io.Serializable;

/**
 * Abstract parent class of all expressions.
 */
public abstract class Expression implements Comparable<Expression>, Serializable {

	/**
	 * Required for serialization.
	 */
	private static final long serialVersionUID = -6176524656345471317L;

	/**
	 * Cached string representation of the expression.
	 */
	private String stringRepresentation = null;

	/**
	 * Abstract method that accepts a visitor. Most {@link Expression}s simply
	 * pre-visits and post-visits the variable.
	 *
	 * @param visitor expression visitor
	 * @throws VisitorException passed on from the visitor
	 */
	public abstract void accept(Visitor visitor) throws VisitorException;

	/**
	 * Compare this expression with another. In the current implementation, all
	 * comparisons are based on the string representation of expressions.
	 *
	 * @param expression potential expression to compare to
	 * @return {@code true} if and only if the expressions have the same string
	 *         representation
	 *
	 * @see java.lang.Comparable#compareTo(java.lang.Object)
	 */
	@Override
	public final int compareTo(Expression expression) {
		return toString().compareTo(expression.toString());
	}

	/**
	 * Abstract method to check if this expression is equal to another. This method
	 * is specified here to force subclasses to provide an implementation.
	 *
	 * @param object potential expression to compare to
	 * @return {@code true} if and only if the expressions are effectively equal
	 *
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public abstract boolean equals(Object object);

	/**
	 * Compute the string representation of the expression. If already computed
	 * before, it is returned immediately. Otherwise, it is computed and stored.
	 *
	 * @return a string representation of the expression
	 *
	 * @see java.lang.Object#toString()
	 */
	@Override
	public final String toString() {
		if (stringRepresentation == null) {
			stringRepresentation = toString0();
		}
		return stringRepresentation;
	}

	/**
	 * Abstract method that returns the string representation of a specific
	 * expression. All subclasses must implement this routine. The usual
	 * {@link #toString()} method takes care of computing the representation only
	 * once.
	 *
	 * @return a string representation of the expression
	 */
	public abstract String toString0();

	/*-- !!! WRONG, REMOVE !!! --*/
	public Double satDelta = 0.0;

}
