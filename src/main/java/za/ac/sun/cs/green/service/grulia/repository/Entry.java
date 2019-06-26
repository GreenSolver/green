package za.ac.sun.cs.green.service.grulia.repository;

/**
 * Parent class for entries stored in a Grulia repository. Such entries are
 * either models (that satisfy some expression), or unsatisfiable cores (that
 * subsume some expression). The models or cores are referred to as "solutions";
 * in fact, solutions can be anything at all, but models and cores are the
 * primary two use cases.
 * 
 * Each entry is also associated with a SatDelta value. This is the SatDelta of
 * the first expression that "generated" the entry. For example, the SatDelta
 * for a model entry, is the SatDelta value of the first expression for which
 * this model was generated.
 * 
 * @date: 2018/06/20
 * @author JH Taljaard (USnr 18509193)
 * @author Willem Visser (2018, 2019)
 * @author Jaco Geldenhuys (2017)
 */
public abstract class Entry implements Comparable<Entry> {

	/**
	 * The SatDelta value of this entry.
	 */
	private final double satDelta;

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
		return Double.compare(getSatDelta(), entry.getSatDelta());
//		int comp = Double.compare(getSatDelta(), entry.getSatDelta());
//		if (comp != 0) {
//			comp = compareTo0(entry);
//		}
//		return comp;
	}

//	public abstract int compareTo0(Entry entry);

	public abstract boolean isValidFor(Entry entry);

//	/**
//	 * Return the solution for this entry.
//	 * 
//	 * @return the entry's solution
//	 */
//	public T getSolution() {
//		return solution;
//	}

//	@Override
//	public int hashCode() {
//		final int prime = 31;
//		int result = 1;
//		String sequence = ((getSATDelta().toString()) + (getSolution().toString()));
//		result = prime * result + sequence.hashCode();
//		return result;
//	}
//
//	@Override
//	public boolean equals(Object obj) {
//		if ((obj == null) || !(obj instanceof Entry)) {
//			return false;
//		}
//		Entry e = (Entry) obj;
//		if (satDelta.equals(e.getSATDelta())) {
//			Object s1 = getSolution();
//			Object s2 = e.getSolution();
//			if ((s1 == null) != (s2 == null)) {
//				return false;
//			}
//			if ((s1 == null) && (s2 == null)) {
//				return true;
//			}
//			if (s1.toString().equals(s2.toString())) {
//				return true;
//			}
//		}
//		return false;
//	}
//
//	@Override
//	public String toString() {
//		return String.format("Entry(SATDelta=%s, {variable, value}=%s)", satDelta, solution.toString());
//	}

}
