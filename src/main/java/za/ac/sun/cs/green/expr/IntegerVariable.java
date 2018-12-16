package za.ac.sun.cs.green.expr;

public class IntegerVariable extends Variable {

	private static final long serialVersionUID = 8942503924718973792L;

	private final Long lowerBound;

	private final Long upperBound;

	public IntegerVariable(String name, long lowerBound, long upperBound) {
		super(name);
		this.lowerBound = lowerBound;
		this.upperBound = upperBound;
	}

	public IntegerVariable(String name, Object original, long lowerBound, long upperBound) {
		super(name, original);
		this.lowerBound = lowerBound;
		this.upperBound = upperBound;
	}
	
	public IntegerVariable(String name, Long lowerBound, Long upperBound) {
		super(name);
		this.lowerBound = lowerBound;
		this.upperBound = upperBound;
	}
	
	public IntegerVariable(String name, Object original, Long lowerBound, Long upperBound) {
		super(name, original);
		this.lowerBound = lowerBound;
		this.upperBound = upperBound;
	}
	
	public Long getLowerBound() {
		return lowerBound;
	}

	public Long getUpperBound() {
		return upperBound;
	}

	@Override
	public void accept(Visitor visitor) throws VisitorException {
		visitor.preVisit(this);
		visitor.postVisit(this);
	}

	@Override
	public boolean equals(Object object) {
		if (object instanceof IntegerVariable) {
			IntegerVariable variable = (IntegerVariable) object;
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
	public String toString() {
		return getName();
	}

}
