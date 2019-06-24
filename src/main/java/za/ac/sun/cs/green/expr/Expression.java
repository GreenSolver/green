package za.ac.sun.cs.green.expr;

import java.io.Serializable;

public abstract class Expression implements Comparable<Expression>, Serializable {

	private static final long serialVersionUID = -6176524656345471317L;

//	private String stringRep = null;

	private String stringRepresentation = null;

	public abstract void accept(Visitor visitor) throws VisitorException;

//    public String getString() {
//        if (stringRep == null) {
//            stringRep = this.toString();
//        }
//        return stringRep;
//    }

	public Double satDelta = 0.0;

	@Override
	public final int compareTo(Expression expression) {
		// TODO
//        return getString().compareTo(expression.getString());
		return toString().compareTo(expression.toString());
	}

	@Override
	public abstract boolean equals(Object object);

	@Override
	public final String toString() {
		if (stringRepresentation == null) {
			stringRepresentation = toString0();
		}
		return stringRepresentation;
	}

	public abstract String toString0();

}
