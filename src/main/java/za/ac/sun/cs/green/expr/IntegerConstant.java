package za.ac.sun.cs.green.expr;

public class IntegerConstant extends Constant {

	private final long value;

	public IntegerConstant(final long value) {
		this.value = value;
	}

	public final long getValue() {
		return value;
	}

	@Override
	public void accept(Visitor visitor) throws VisitorException {
		visitor.preVisit(this);
		visitor.postVisit(this);
	}

	@Override
	public boolean equals(Object object) {
		if (object instanceof IntegerConstant) {
			IntegerConstant constant = (IntegerConstant) object;
			return value == constant.value;
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return Long.hashCode(value);
	}

	@Override
	public String toString() {
		return Long.toString(value);
	}

}
