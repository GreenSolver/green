package za.ac.sun.cs.green.expr;

@Deprecated
public class IntegerConstant extends Constant {

	private static final long serialVersionUID = -188232380713969220L;

	public static final Constant ZERO32 = new IntegerConstant(0, 32);
    public static final Constant ZERO64 = new IntegerConstant(0, 64);
    public static final Constant ONE32 = new IntegerConstant(1, 32);
    public static final Constant ONE64 = new IntegerConstant(1, 64);

	private final long value;
	private final int size;

    public IntegerConstant(final long value, final int size) {
        this.value = value;
        this.size = size;
    }

    public long getValue() {
        return value;
    }

    public int getSize() {
        return size;
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
