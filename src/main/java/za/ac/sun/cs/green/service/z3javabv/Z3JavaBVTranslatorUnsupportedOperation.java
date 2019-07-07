package za.ac.sun.cs.green.service.z3javabv;

import za.ac.sun.cs.green.expr.VisitorException;

/**
 * Indicates that an expression cannot be translated because it contains an
 * operation that is not supported by the translator.
 */
public class Z3JavaBVTranslatorUnsupportedOperation extends VisitorException {

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
	Z3JavaBVTranslatorUnsupportedOperation(String message) {
		super(message);
	}

}
