package za.ac.sun.cs.green.expr;

@Deprecated
public class IntegerVariable extends Variable {

	private static final long serialVersionUID = 8942503924718973792L;

    protected final Long lowerBound;
    protected final Long upperBound;
    protected final Integer size;

	public IntegerVariable(String name, long lowerBound, long upperBound, int size) {
		super(name);
		this.lowerBound = lowerBound;
		this.upperBound = upperBound;
        this.size = size;
    }

	public IntegerVariable(String name, Object original, long lowerBound, long upperBound, int size) {
		super(name, original);
		this.lowerBound = lowerBound;
		this.upperBound = upperBound;
        this.size = size;
    }
	
	public IntegerVariable(String name, Long lowerBound, Long upperBound, Integer size) {
		super(name);
		this.lowerBound = lowerBound;
		this.upperBound = upperBound;
        this.size = size;
    }
	
	public IntegerVariable(String name, Object original, Long lowerBound, Long upperBound, Integer size) {
		super(name, original);
		this.lowerBound = lowerBound;
		this.upperBound = upperBound;
        this.size = size;
    }

	public Long getLowerBound() {
		return lowerBound;
	}

	public Long getUpperBound() {
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
