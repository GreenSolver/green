package za.ac.sun.cs.green.service.grulia;

/**
 * @author: Andrea Aquino.
 *
 * Description:
 * Pair of values.
 */
public class Pair<L, R> {
    private L l;
    private R r;

    /**
     * Creates a new pair of two objects.
     *
     * @param l
     *           the first component of the pair.
     * @param r
     *           the second component of the pair.
     */
    public Pair(L l, R r) {
        this.l = l;
        this.r = r;
    }

    /**
     * Returns the first component of the pair.
     *
     * @return the first component of the pair.
     */
    public L getL() {
        return l;
    }

    /**
     * Returns the second component of the pair.
     *
     * @return the second component of the pair.
     */
    public R getR() {
        return r;
    }

    /**
     * Updates the first component of the pair.
     *
     * @param l
     *           the new value for the first component of the pair.
     */
    public void setL(L l) {
        this.l = l;
    }

    /**
     * Updates the second component of the pair.
     *
     * @param r
     *           the new value for the second component of the pair.
     */
    public void setR(R r) {
        this.r = r;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((l == null) ? 0 : l.hashCode());
        result = prime * result + ((r == null) ? 0 : r.hashCode());
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
            if (l == null) {
                if (o.l != null) {
                    return false;
                }
            } else if (!l.equals(o.l)) {
                return false;
            }
            if (r == null) {
                if (o.r != null) {
                    return false;
                }
            } else if (!r.equals(o.r)) {
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
