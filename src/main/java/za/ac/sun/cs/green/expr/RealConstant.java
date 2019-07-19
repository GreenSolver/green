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
 * Representation of a real constant.
 */
public class RealConstant extends Constant {

	/**
	 * Required for serialization.
	 */
	private static final long serialVersionUID = 5342850784343698801L;

	/**
	 * The value of the constant.
	 */
	protected final double value;

	/**
	 * Construct a real constant with the given value.
	 * 
	 * @param value value of the constant
	 */
	public RealConstant(final double value) {
		this.value = value;
	}

	/**
	 * Return the value of the constant.
	 *
	 * @return value of the constant
	 */
	public final double getValue() {
		return value;
	}

	/**
	 * Accept a visitor. As with other {@link Expression} final classes, it
	 * straightforwardly pre-visits and post-visits the constant.
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
	 * Checks if this constant is equal to another. Constants are equal if and only
	 * if they have the same value.
	 *
	 * @param object potential constant to compare to
	 * @return {@code true} if and only if the constants have the same value
	 *
	 * @see za.ac.sun.cs.green.expr.Expression#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object object) {
		if (object instanceof RealConstant) {
			RealConstant constant = (RealConstant) object;
			return value == constant.value;
		} else {
			return false;
		}
	}

	/**
	 * Return a hash code for the constant based on its value.
	 *
	 * @return constant hash code
	 *
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		return Double.hashCode(value);
	}

	/**
	 * Return a string representation of the variable, which amounts to its value.
	 *
	 * @return string representation
	 *
	 * @see za.ac.sun.cs.green.expr.Expression#toString0()
	 */
	@Override
	public String toString0() {
		return Double.toString(value);
	}

}
