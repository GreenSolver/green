/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.util;

/**
 * Generic pair of values.
 *
 * Based on code by Andrea Aquino.
 *
 * @param <L> type of first component
 * @param <R> type of second component
 */
public class Pair<L, R> {

	/**
	 * First component of pair.
	 */
	private L left;

	/**
	 * Second component of pair.
	 */
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

	/**
	 * Return a hash code for the pair based on the hash codes of the components.
	 *
	 * @return hash code for the pair
	 *
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((left == null) ? 0 : left.hashCode());
		result = prime * result + ((right == null) ? 0 : right.hashCode());
		return result;
	}

	/**
	 * Checks if this pair is equal to another pair based on the equality of the components.
	 *
	 * @param other other (potential) pair
	 * @return {@code true} if and only if the pairs are equal
	 *
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
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

	/**
	 * Return a string representation for the pair.
	 *
	 * @return string representation of pair
	 *
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return String.format("(%s, %s)", this.getL(), this.getR());
	}

}
