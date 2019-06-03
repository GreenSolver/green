package za.ac.sun.cs.green.expr;

import java.io.Serializable;

public abstract class Expression implements Comparable<Expression>, Serializable {

    private String stringRep = null;
    public abstract void accept(Visitor visitor) throws VisitorException;

    public String getString() {
        if (stringRep == null) {
            stringRep = this.toString();
        }
        return stringRep;
    }

    public Double satDelta = 0.0;

    @Override
    public final int compareTo(Expression expression) {
        // TODO
        return getString().compareTo(expression.getString());
    }

    @Override
    public abstract boolean equals(Object object);

    @Override
    public abstract String toString();

}
