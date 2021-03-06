/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.expr;

/**
 * Representation of a real variable.
 */
public class RealVariable extends Variable {

	/**
	 * Required for serialization.
	 */
	private static final long serialVersionUID = -8815803703741978839L;

	/**
	 * Least value this variable is allowed to assume.
	 */
	protected final Double lowerBound;

	/**
	 * Greatest value this variable is allowed to assume.
	 */
	protected final Double upperBound;

	/**
	 * Construct a real variable with the given name, and lower and upper bounds.
	 *
	 * @param name       new variable name
	 * @param lowerBound lower bound for the new variable
	 * @param upperBound upper bound for the new variable
	 */
	public RealVariable(final String name, final Double lowerBound, final Double upperBound) {
		super(name);
		this.lowerBound = lowerBound;
		this.upperBound = upperBound;
	}

	/**
	 * Construct a real variable with the given name, lower and upper bounds, and
	 * associated origin variable.
	 *
	 * @param name       new variable name
	 * @param original   associated origin variable
	 * @param lowerBound lower bound for the new variable
	 * @param upperBound upper bound for the new variable
	 */
	public RealVariable(final String name, final Object original, final Double lowerBound, final Double upperBound) {
		super(name, original);
		this.lowerBound = lowerBound;
		this.upperBound = upperBound;
	}

	/**
	 * Return the lower bound for the variable.
	 *
	 * @return variable lower bound
	 */
	public Double getLowerBound() {
		return lowerBound;
	}

	/**
	 * Return the upper bound for the variable.
	 *
	 * @return variable upper bound
	 */
	public Double getUpperBound() {
		return upperBound;
	}

	/**
	 * Accept a visitor. As with other {@link Expression} final classes, it
	 * straightforwardly pre-visits and post-visits the variable.
	 *
	 * @param visitor expression visitor
	 * @throws VisitorException passed on from the visitor
	 *
	 * @see za.ac.sun.cs.green.expr.Expression#accept(za.ac.sun.cs.green.expr.Visitor)
	 */
	@Override
	public void accept(Visitor visitor) throws VisitorException {
		visitor.preVisit(this);
		visitor.postVisit(this);
	}

	/**
	 * Checks if this variable is equal to another. Variables are equal if and only
	 * if they have the same name.
	 *
	 * @param object potential variable to compare to
	 * @return {@code true} if and only if the variables have the same name
	 *
	 * @see za.ac.sun.cs.green.expr.Expression#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object object) {
		if (object instanceof RealVariable) {
			RealVariable variable = (RealVariable) object;
			return getName().equals(variable.getName());
		} else {
			return false;
		}
	}

	/**
	 * Return a hash code for the variable based on its name.
	 *
	 * @return variable hash code
	 *
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		return getName().hashCode();
	}

	/**
	 * Return a string representation of the variable, which amounts to its name.
	 *
	 * @return string representation
	 *
	 * @see za.ac.sun.cs.green.expr.Expression#toString0()
	 */
	@Override
	public String toString0() {
		return getName();
	}

}
