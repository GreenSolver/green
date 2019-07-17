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
 * Representation of a string variable.
 */
public class StringVariable extends Variable {

	/**
	 * Required for serialization.
	 */
	private static final long serialVersionUID = -4405246046006773012L;

	/**
	 * Construct a string variable with the given name.
	 * 
	 * @param name new variable name
	 */
	public StringVariable(final String name) {
		super(name);
	}

	/**
	 * Construct a boolean variable with the given name and associated origin
	 * variable.
	 * 
	 * @param name     new variable name
	 * @param original associated origin variable
	 */
	public StringVariable(final String name, final Object original) {
		super(name, original);
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
		if (object instanceof StringVariable) {
			StringVariable variable = (StringVariable) object;
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
