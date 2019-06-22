package za.ac.sun.cs.green.expr;

public class BoolVariable extends Variable {

	private static final long serialVersionUID = -2204726850649411139L;

	public BoolVariable(String name) {
		super(name);
	}

	@Override
	public void accept(Visitor visitor) throws VisitorException {
		// placeholder
	}

	@Override
	public int hashCode() {
		return getName().hashCode();
	}

	@Override
	public boolean equals(Object object) {
		// placeholder
		return false;
	}

	@Override
	public String toString() {
		// placeholder
		return null;
	}

}
