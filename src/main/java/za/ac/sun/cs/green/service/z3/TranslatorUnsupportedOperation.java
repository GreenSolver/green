package za.ac.sun.cs.green.service.z3;

import za.ac.sun.cs.green.expr.VisitorException;

public class TranslatorUnsupportedOperation extends VisitorException {

	private static final long serialVersionUID = 7637864816254294177L;

	public TranslatorUnsupportedOperation(String message) {
		super(message);
	}

}
