package za.ac.sun.cs.green.service.barvinok;

import za.ac.sun.cs.green.expr.VisitorException;

@SuppressWarnings("serial")
class TranslatorUnsupportedOperation extends VisitorException {

	TranslatorUnsupportedOperation(String message) {
		super(message);
	}

}
