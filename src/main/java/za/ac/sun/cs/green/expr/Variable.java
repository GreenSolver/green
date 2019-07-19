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
 * Abstract parent class of variables.
 */
public abstract class Variable extends Expression implements Serializable {

	/**
	 * Required for serialization.
	 */
	private static final long serialVersionUID = -1712398155778326862L;

	/**
	 * Name of the variable.
	 */
	protected final String name;

	/**
	 * Some associated origin variable. This is often {@code null}.
	 */
	protected final Object original;

	/**
	 * Construct a variable with the given name.
	 * 
	 * @param name new variable name
	 */
	public Variable(final String name) {
		this.name = name;
		this.original = null;
	}

	/**
	 * Construct a variable with the given name and associated origin variable.
	 * 
	 * @param name     new variable name
	 * @param original associated origin variable
	 */
	public Variable(final String name, final Object original) {
		this.name = name;
		this.original = original;
	}

	/**
	 * Return the name of the variable.
	 *
	 * @return name of the variable
	 */
	public final String getName() {
		return name;
	}

	/**
	 * Return the associated origin variable.
	 *
	 * @return associated origin variable
	 */
	public final Object getOriginal() {
		return original;
	}

}
