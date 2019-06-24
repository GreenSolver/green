package za.ac.sun.cs.green.util;

/**
 * Pair of values.
 *
 * @author: Andrea Aquino
 * @author: Jaco Geldenhuys <geld@sun.ac.za> (contibutor)
 */
public class Pair<L, R> {

	private L left;
	private R right;

	/**
	 * Creates a new pair of two objects.
	 *
	 * @param left  the first component of the pair.
	 * @param right the second component of the pair.
	 */
	public Pair(L left, R right) {
		this.left = left;
		this.right = right;
	}

	/**
	 * Returns the first component of the pair.
	 *
	 * @return the first component of the pair.
	 */
	public L getL() {
		return left;
	}

	/**
	 * Returns the second component of the pair.
	 *
	 * @return the second component of the pair.
	 */
	public R getR() {
		return right;
	}

	/**
	 * Updates the first component of the pair.
	 *
	 * @param left the new value for the first component of the pair.
	 */
	public void setL(L left) {
		this.left = left;
	}

	/**
	 * Updates the second component of the pair.
	 *
	 * @param right the new value for the second component of the pair.
	 */
	public void setR(R right) {
		this.right = right;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((left == null) ? 0 : left.hashCode());
		result = prime * result + ((right == null) ? 0 : right.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object other) {
		if (this == other) {
			return true;
		} else if (other == null) {
			return false;
		} else if (getClass() != other.getClass()) {
			return false;
		} else {
			Pair<?, ?> o = (Pair<?, ?>) other;
			if (left == null) {
				if (o.left != null) {
					return false;
				}
			} else if (!left.equals(o.left)) {
				return false;
			}
			if (right == null) {
				if (o.right != null) {
					return false;
				}
			} else if (!right.equals(o.right)) {
				return false;
			}
			return true;
		}
	}

	@Override
	public String toString() {
		return String.format("(%s, %s)", this.getL(), this.getR());
	}

}
