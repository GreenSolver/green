/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.choco4;

import za.ac.sun.cs.green.expr.VisitorException;

/**
 * Exception thrown when Choco4 cannot model a GREEN expression.
 */
public class TranslatorUnsupportedOperation extends VisitorException {

	/**
	 * Required for serialization.
	 */
	private static final long serialVersionUID = 8983159590749693867L;

	/**
	 * Construct a Choco4 exception to indicate that an operation is not supported.
	 * 
	 * @param message
	 *                exception message
	 */
	public TranslatorUnsupportedOperation(String message) {
		super(message);
	}

}
