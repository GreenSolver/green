package za.ac.sun.cs.green.service.grulia;

import java.io.Serializable;

/**
 * @date: 2018/06/20
 * @author: JH Taljaard. Student Number: 18509193. Supervisor: Willem Visser
 *          (2018,2019), Jaco Geldenhuys (2017)
 *
 *          Description: Parent class for Entry stored in the Repo.
 */
public abstract class Entry implements Comparable<Entry>, Serializable {

	private static final long serialVersionUID = -7109986504181068193L;

	/**
	 * The SAT-Delta value
	 */
	protected final Double satDelta;

	/**
	 * The solution can be a Map of the models or set of Expression of the
	 * unsat-core
	 */
	protected Object solution;

	public Entry(Double satDelta, Object solution) {
		this.satDelta = satDelta;
		this.solution = solution;
	}

	public abstract Object getSolution();

	/**
	 * @return Number of variables (in sat case)
	 */
	public abstract int getSize();

	public Double getSATDelta() {
		return satDelta;
	}

	public int equals(Entry e1) {
		if (this.getSolution() == null || e1.getSolution() == null) {
			return 1;
		}
		return (this.hashCode() == e1.hashCode()) ? 0 : 1;
	}

	@Override
	public int compareTo(Entry e2) {
		double referenceScore = 0.0;
		Double e1Delta = Math.abs(referenceScore - this.getSATDelta());
		Double e2Delta = Math.abs(referenceScore - e2.getSATDelta());
		int comp = e1Delta.compareTo(e2Delta);
		return (comp != 0) ? comp : this.equals(e2);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		String sequence = ((getSATDelta().toString()) + (getSolution().toString()));
		result = prime * result + sequence.hashCode();
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if ((obj == null) || !(obj instanceof Entry)) {
			return false;
		}
		Entry e = (Entry) obj;
		if (satDelta.equals(e.getSATDelta())) {
			Object s1 = getSolution();
			Object s2 = e.getSolution();
			if ((s1 == null) != (s2 == null)) {
				return false;
			}
			if ((s1 == null) && (s2 == null)) {
				return true;
			}
			if (s1.toString().equals(s2.toString())) {
				return true;
			}
		}
		return false;
	}

	@Override
	public String toString() {
		return String.format("Entry(SATDelta=%s, {variable, value}=%s)", satDelta, solution.toString());
	}

}
