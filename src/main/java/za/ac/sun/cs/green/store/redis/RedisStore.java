/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.store.redis;

import java.io.IOException;
import java.io.Serializable;
import java.util.Properties;
import java.util.Set;

import redis.clients.jedis.Jedis;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.store.BasicStore;
import za.ac.sun.cs.green.store.Store;
import za.ac.sun.cs.green.util.Configuration;
import za.ac.sun.cs.green.util.Reporter;

/**
 * An implementation of a {@link Store} based on redis
 * (<a href="http://www.redis.io"><code>http://www.redis.io</code></a>).
 */
public class RedisStore extends BasicStore {

	// ======================================================================
	//
	// CONSTANTS THAT DEFINE THE BEHAVIOUR OF REDIS
	//
	// ======================================================================

	/**
	 * The time (in seconds) of inactivity until the connection to the redis store
	 * timeout.
	 */
	private static final int TIMEOUT = 2000;

	/**
	 * The default host of the redis server.
	 */
	private static final String DEFAULT_REDIS_HOST = "localhost";

	/**
	 * Options passed to the LattE executable.
	 */
	private static final int DEFAULT_REDIS_PORT = 6379;

	// ======================================================================
	//
	// COUNTERS
	//
	// ======================================================================

	/**
	 * Number of times {@code get())} is called.
	 */
	protected int getCount = 0;

	/**
	 * Number of times {@code put()} is called.
	 */
	protected int putCount = 0;

	// ======================================================================
	//
	// TIME CONSUMPTION
	//
	// ======================================================================

	/**
	 * Milliseconds spent on operations.
	 */
	protected long storeTimeConsumption = 0;

	/**
	 * Milliseconds spent on {@code get()} operations.
	 */
	protected long getTimeConsumption = 0;

	/**
	 * Milliseconds spent on {@code put()} operations.
	 */
	protected long putTimeConsumption = 0;

	// ======================================================================
	//
	// FIELDS
	//
	// ======================================================================

	/**
	 * Connection to the redis store.
	 */
	protected Jedis db = null;

	// ======================================================================
	//
	// CONSTRUCTOR & METHODS
	//
	// ======================================================================

	/**
	 * Construct a redis store. Note that the connection to a running redis database
	 * is not established until the {@link #setName(String)} method is invoked.
	 * 
	 * @param solver
	 *               associated GREEN solver
	 */
	public RedisStore(Green solver) {
		super(solver);
	}

	/**
	 * Look up the host and port in the GREEN properties and make a connection to
	 * the redis server. If the name is {@code null}, the property prefix
	 * "green.redis" is used. Otherwise, the prefix "green.store.XYZ" is used, where
	 * "XYZ" is the store name.
	 *
	 * @param name
	 *             store name or {@code null}
	 *
	 * @see za.ac.sun.cs.green.store.BasicStore#setName(java.lang.String)
	 */
	@Override
	public void setName(final String name) {
		Properties properties = solver.getProperties();
		String prefix = (name != null) ? "green.store." + name : "green.redis";
		String host = properties.getProperty(prefix + ".host", DEFAULT_REDIS_HOST);
		int port = Configuration.getIntegerProperty(properties, prefix + ".port", DEFAULT_REDIS_PORT);
		db = new Jedis(host, port, TIMEOUT);
	}

	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("getCount", getCount);
		reporter.report("putCount", putCount);
		reporter.report("storeTimeConsumption", storeTimeConsumption);
		reporter.report("  getTimeConsumption", getTimeConsumption);
		reporter.report("  putTimeConsumption", putTimeConsumption);
	}

	@Override
	public synchronized Object get(String key) {
		long startTime = System.currentTimeMillis();
		getCount++;
		try {
			String value = db.get(key);
			getTimeConsumption += System.currentTimeMillis() - startTime;
			storeTimeConsumption += System.currentTimeMillis() - startTime;
			return (value == null) ? null : fromString(value);
		} catch (IOException x) {
			log.fatal("io problem", x);
		} catch (ClassNotFoundException x) {
			log.fatal("class not found problem", x);
		}
		getTimeConsumption += System.currentTimeMillis() - startTime;
		storeTimeConsumption += System.currentTimeMillis() - startTime;
		return null;
	}

	@Override
	public synchronized void put(String key, Serializable value) {
		long startTime = System.currentTimeMillis();
		putCount++;
		try {
			db.set(key, toString(value));
		} catch (IOException x) {
			log.fatal("io problem", x);
		}
		putTimeConsumption += System.currentTimeMillis() - startTime;
		storeTimeConsumption += System.currentTimeMillis() - startTime;
	}

	@Override
	public Set<String> keySet() {
		return db.keys("*");
	}

	@Override
	public void clear() {
		long startTime = System.currentTimeMillis();
		try {
			db.flushAll();
		} catch (Exception e) {
		}
		storeTimeConsumption += System.currentTimeMillis() - startTime;
	}

}
