/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.store;

import java.io.Serializable;
import java.util.Collections;
import java.util.Set;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.util.Reporter;

/**
 * A dummy store that does not store any values and always returns {@code null}
 * to indicate that keys have not been found. This is useful in context where a
 * store is required but we do not really want to store anything.
 */
public class NullStore extends BasicStore {

	/**
	 * Number of times a "get" operation has been invoked.
	 */
	private int getCount = 0;

	/**
	 * Number of times a "put" operation has been invoked.
	 */
	private int putCount = 0;

	/**
	 * Create an instance of the dummy store.
	 * 
	 * @param solver
	 *               associated GREEN solver
	 */
	public NullStore(final Green solver) {
		super(solver);
	}

	/**
	 * Report collected statistics.
	 *
	 * @param reporter
	 *                 reporting mechanism
	 *
	 * @see za.ac.sun.cs.green.store.Store#report(za.ac.sun.cs.green.util.Reporter)
	 */
	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("getCount", getCount);
		reporter.report("putCount", putCount);
	}

	/**
	 * Insert a key-value pair in the dummy store by ignoring the pair and simply
	 * counting the method invocation.
	 *
	 * @param key
	 *            key for the associated value
	 * @return always {@code null}
	 *
	 * @see za.ac.sun.cs.green.store.Store#get(java.lang.String)
	 */
	@Override
	public Object get(String key) {
		getCount++;
		return null;
	}

	/**
	 * Look up a key-value pair in the dummy store by counting the method invocation
	 * and ignoring the parameters.
	 *
	 * @param key
	 *              key for the associated value (ignored)
	 * @param value
	 *              value associated with the key (ignored)
	 *
	 * @see za.ac.sun.cs.green.store.Store#put(java.lang.String,
	 *      java.io.Serializable)
	 */
	@Override
	public void put(String key, Serializable value) {
		putCount++;
	}

	/**
	 * Return an empty set of keys.
	 *
	 * @return empty set
	 *
	 * @see za.ac.sun.cs.green.store.Store#keySet()
	 */
	@Override
	public Set<String> keySet() {
		return Collections.emptySet();
	}

	/**
	 * Do nothing.
	 *
	 * @see za.ac.sun.cs.green.store.BasicStore#flushAll()
	 */
	@Override
	public void flushAll() {
	}

	/**
	 * Do nothing.
	 *
	 * @see za.ac.sun.cs.green.store.Store#clear()
	 */
	@Override
	public void clear() {
	}

	/**
	 * Do nothing.
	 *
	 * @see za.ac.sun.cs.green.store.BasicStore#shutdown()
	 */
	@Override
	public void shutdown() {
	}

}
