package za.ac.sun.cs.green.service.grulia;

/**
 * Parent class for entries stored in a Grulia repository. Such entries are
 * either models (that satisfy some expression), or unsatisfiable cores (that
 * subsume some expression). The models or cores are referred to as "solutions";
 * in fact, solutions can be anything at all, but models and cores are the
 * primary two use cases.
 * <p>
 * Each entry is also associated with a SatDelta value. This is the SatDelta of
 * the first expression that "generated" the entry. For example, the SatDelta
 * for a model entry, is the SatDelta value of the first expression for which
 * this model was generated.
 *
 * @author JH Taljaard (USnr 18509193)
 * @author Willem Visser (2018, 2019)
 * @author Jaco Geldenhuys (2017)
 * @date: 2018/06/20
 */
public abstract class Entry implements Comparable<Entry> {

	/**
	 * The SatDelta value of this entry.
	 */
	private final double satDelta;

	/**
	 * String representation for this entry.
	 */
	private String stringRepresentation = null;

	/**
	 * Construct an entry.
	 *
	 * @param satDelta SatDelta value for the new entry
	 */
	public Entry(double satDelta) {
		this.satDelta = satDelta;
	}

	/**
	 * Return the SatDelta value for this entry.
	 *
	 * @return the entry's SatDelta value
	 */
	public double getSatDelta() {
		return satDelta;
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see java.lang.Comparable#compareTo(java.lang.Object)
	 */
	@Override
	public int compareTo(Entry entry) {
		return toString().compareTo(entry.toString());
	}

	/**
	 * Determine if the current entry is "valid" for the given entry.  This means that this entry could be used
	 * as a model/core/solution for the given entry.  For example, in the case of models, this model could be
	 * valid if it has enough variables.
	 *
	 * @param entry target entry
	 * @return {@code true} if this entry can be used, otherwise {@code false}
	 */
	public abstract boolean isValidFor(Entry entry);

	@Override
	public final String toString() {
		if (stringRepresentation == null) {
			StringBuilder s = new StringBuilder();
			s.append("(satDelta=").append(getSatDelta());
			s.append(", ").append(toString0());
			s.append(')');
			stringRepresentation = s.toString();
		}
		return stringRepresentation;
	}

	/**
	 * Return a string representation for this entry.
	 *
	 * @return a string representation for this entrty
	 */
	public abstract String toString0();

//	public int hashCode() {
//	public boolean equals(Object obj) {

}
