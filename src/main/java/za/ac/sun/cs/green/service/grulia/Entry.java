/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
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
 */
public abstract class Entry implements Comparable<Entry> {

	/**
	 * The SatDelta value of this entry.
	 */
	private final double satDelta;

	/**
	 * The size of the model/core stored in this entry.
	 */
	private final int size;

	/**
	 * String representation for this entry.
	 */
	private String stringRepresentation = null;

	/**
	 * Construct an entry.
	 *
	 * @param satDelta
	 *                 SatDelta value for the new entry
	 */
	public Entry(final double satDelta, final int size) {
		this.satDelta = satDelta;
		this.size = size;
	}

	/**
	 * Return the SatDelta value for this entry.
	 *
	 * @return the entry's SatDelta value
	 */
	public double getSatDelta() {
		return satDelta;
	}

	/**
	 * Return the size for this entry.
	 *
	 * @return the entry's size
	 */
	public int getSize() {
		return size;
	}

	/**
	 * Compare this entry to another. The comparison is based firstly on the
	 * satDelta value, then the size of model/core, and finally on the string
	 * representations of the entries.
	 *
	 * @param entry
	 *              entry to compare to
	 * @return result of comparison
	 *
	 * @see java.lang.Comparable#compareTo(java.lang.Object)
	 */
	@Override
	public int compareTo(Entry entry) {
		int result = Double.compare(getSatDelta(), entry.getSatDelta());
		if (result == 0) {
			result = Integer.compare(getSize(), entry.getSize());
			if (result == 0) {
				result = toString().compareTo(entry.toString());
			}
		}
		return result;
	}

	/**
	 * Determine if the current entry is "valid" for the given entry. This means
	 * that this entry could be used as a model/core/solution for the given entry.
	 * For example, in the case of models, this model could be valid if it has
	 * enough variables.
	 *
	 * @param entry
	 *              target entry
	 * @return {@code true} if this entry can be used, otherwise {@code false}
	 */
	public abstract boolean isValidFor(Entry entry);

	/**
	 * Create, if it does not exist, and return the string representation of the
	 * entry. The creation is done only once and stored in
	 * {@link #stringRepresentation}.
	 *
	 * @return string representation of entry
	 *
	 * @see java.lang.Object#toString()
	 */
	@Override
	public final String toString() {
		if (stringRepresentation == null) {
			StringBuilder s = new StringBuilder();
			s.append("(satDelta=").append(getSatDelta());
			s.append(", size=").append(getSize());
			s.append(", ").append(toString0());
			s.append(')');
			stringRepresentation = s.toString();
		}
		return stringRepresentation;
	}

	/**
	 * Return a string representation for this entry.
	 *
	 * @return a string representation for this entry
	 */
	public abstract String toString0();

}
