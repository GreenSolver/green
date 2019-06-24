package za.ac.sun.cs.green.expr;

public class RealVariable extends Variable {

	private static final long serialVersionUID = -8815803703741978839L;

    protected final Double lowerBound;
    protected final Double upperBound;
    protected final Integer size;

	public RealVariable(String name, Object original, Double lowerBound, Double upperBound, Integer size) {
		super(name, original);
		this.lowerBound = lowerBound;
		this.upperBound = upperBound;
		this.size = size;
	}
	
	public RealVariable(String name, Double lowerBound, Double upperBound, Integer size) {
		super(name);
		this.lowerBound = lowerBound;
		this.upperBound = upperBound;
        this.size = size;
    }

	public Double getLowerBound() {
		return lowerBound;
	}

	public Double getUpperBound() {
		return upperBound;
	}

	public Integer getSize() {
	    return size;
    }

	@Override
	public void accept(Visitor visitor) throws VisitorException {
		visitor.preVisit(this);
		visitor.postVisit(this);
	}

//	@Override
//	public int compareTo(Expression expression) {
//		RealVariable variable = (RealVariable) expression;
//		return getName().compareTo(variable.getName());
//	}

	@Override
	public boolean equals(Object object) {
		if (object instanceof RealVariable) {
			RealVariable variable = (RealVariable) object;
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
