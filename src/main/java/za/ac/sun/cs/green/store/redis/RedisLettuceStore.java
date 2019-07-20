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
import java.util.HashSet;
import java.util.Properties;
import java.util.Set;

import io.lettuce.core.RedisClient;
import io.lettuce.core.api.StatefulRedisConnection;
import io.lettuce.core.api.async.RedisAsyncCommands;
import io.lettuce.core.api.sync.RedisCommands;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.store.BasicStore;
import za.ac.sun.cs.green.store.Store;
import za.ac.sun.cs.green.util.Configuration;
import za.ac.sun.cs.green.util.Reporter;

/**
 * An implementation of a {@link Store} based on Lettuce
 * (<a href="https://lettuce.io"><code>https://lettuce.io</code></a>)
 * that connects to a redis server
 * (<a href="http://www.redis.io"><code>http://www.redis.io</code></a>).
 */
public class RedisLettuceStore extends BasicStore {

	// ======================================================================
	//
	// CONSTANTS THAT DEFINE THE BEHAVIOUR OF REDIS
	//
	// ======================================================================

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
	 * Representation of the Redis client.
	 */
	private RedisClient redisClient;

	/**
	 * Connection to the Redis server.
	 */
	private StatefulRedisConnection<String, String> redisConnection;

	/**
	 * Synchronous Redis command channel.
	 */
	private RedisCommands<String, String> syncCommands;

	/**
	 * Asynchronous Redis command channel.
	 */
	private RedisAsyncCommands<String, String> asyncCommands;

	// ======================================================================
	//
	// CONSTRUCTOR & METHODS
	//
	// ======================================================================

	/**
	 * Construct a lettuce store. Note that the connection to a running redis database
	 * is not established until the {@link #setName(String)} method is invoked.
	 * 
	 * @param solver
	 *               associated GREEN solver
	 */
	public RedisLettuceStore(Green solver) {
		super(solver);
	}

	@Override
	public void setName(final String name) {
		Properties properties = solver.getProperties();
		String prefix = (name != null) ? "green.store." + name : "green.redis";
		String host = properties.getProperty(prefix + ".host", DEFAULT_REDIS_HOST);
		int port = Configuration.getIntegerProperty(properties, prefix + ".port", DEFAULT_REDIS_PORT);
		redisClient = RedisClient.create("redis://" + host + ":" + port + "/0");
		redisConnection = redisClient.connect();
		syncCommands = redisConnection.sync();
		asyncCommands = redisConnection.async();
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
			String value = syncCommands.get(key);
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
			asyncCommands.set(key, toString(value));
		} catch (IOException x) {
			log.fatal("io problem", x);
		}
		putTimeConsumption += System.currentTimeMillis() - startTime;
		storeTimeConsumption += System.currentTimeMillis() - startTime;
	}

	public void flushAll() {
		long startTime = System.currentTimeMillis();
		asyncCommands.flushCommands();
		storeTimeConsumption += System.currentTimeMillis() - startTime;
	}

	@Override
	public void clear() {
		long startTime = System.currentTimeMillis();
		syncCommands.flushallAsync();
		storeTimeConsumption += System.currentTimeMillis() - startTime;
	}

	@Override
	public Set<String> keySet() {
		long startTime = System.currentTimeMillis();
		Set<String> keySet = new HashSet<>(syncCommands.keys("*"));
		storeTimeConsumption += System.currentTimeMillis() - startTime;
		return keySet;
	}

}
