package za.ac.sun.cs.green.expr;

public class BoolVariable extends Variable {

	private static final long serialVersionUID = -2204726850649411139L;

	public BoolVariable(String name) {
		super(name);
	}

	@Override
	public void accept(Visitor visitor) throws VisitorException {
		visitor.preVisit(this);
		visitor.postVisit(this);
	}

	@Override
	public boolean equals(Object object) {
		if (object instanceof IntVariable) {
			IntVariable variable = (IntVariable) object;
			return getName().equals(variable.getName());
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return getName().hashCode();
	}

	@Override
	public String toString0() {
		return getName();
	}

}
