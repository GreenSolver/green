/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.smtlib;

import za.ac.sun.cs.green.expr.VisitorException;

/**
 * Indicates that an expression cannot be translated because it contains an
 * operation that is not supported by the translator.
 */
public class TranslatorUnsupportedOperation extends VisitorException {

	/**
	 * Generate serial ID for serialization.
	 */
	private static final long serialVersionUID = 2796868255898233414L;

	/**
	 * Construct an exception to indicate that an expression cannot be translated
	 * because it contains an operation that is not supported by the translator.
	 * 
	 * @param message more details about the error
	 */
	TranslatorUnsupportedOperation(String message) {
		super(message);
	}

}
