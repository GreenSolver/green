/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.grulia;

import java.util.List;

/**
 * Interface for a Grulia in-memory store for entries.
 * 
 * @param <E> specific type of entry stored
 */
public interface Repository<E extends Entry> {

	/**
	 * Return the number of entries in the repository.
	 *
	 * @return numbe of entries
	 */
	int size();

	/**
	 * Add a new entry to the repository.
	 *
	 * @param entry new entry
	 */
	void add(E entry);

	/**
	 * Return a list of all entries that are within a given distance of a starting point.
	 *
	 * @param limit how far from starting point to search
	 * @param startingPoint starting point
	 * @return list of close entries
	 */
	List<E> getEntries(int limit, E startingPoint);
	
	/**
	 * Return a list of all entries.
	 *
	 * @return list of entries
	 */
	List<E> getAllEntries();

	/**
	 * Remove all entries from repository.
	 */
	void clear();
	
}
