package za.ac.sun.cs.green.service.choco4;

import za.ac.sun.cs.green.expr.VisitorException;

@SuppressWarnings("serial")
public class TranslatorUnsupportedOperation extends VisitorException {

	public TranslatorUnsupportedOperation(String message) {
		super(message);
	}

}
