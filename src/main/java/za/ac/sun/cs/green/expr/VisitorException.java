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
 * Exception thrown by a visitor.
 */
public class VisitorException extends Exception {

	/**
	 * Required for serialization.
	 */
	private static final long serialVersionUID = 3836945988367658587L;

	/**
	 * Construct a visitor exception.
	 * 
	 * @param message exception message
	 */
	public VisitorException(String message) {
		super(message);
	}

}
