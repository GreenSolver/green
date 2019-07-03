package za.ac.sun.cs.green.store.memstore;

import java.io.Serializable;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;
import java.util.Set;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.store.BasicStore;
import za.ac.sun.cs.green.store.redis.RedisStore;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Implementation of a {@link BasicStore} that caches its results in memory and
 * falls back on a {@link RedisStore}. At the end of Green's use, the cached
 * results are flushed back to redis.
 */
public class MemStore extends BasicStore {

	/**
	 * The in-memory cache.
	 */
	protected final Map<String, Object> db = new HashMap<String, Object>();

	/**
	 * The redis store to fall back on.
	 */
	protected final RedisStore redisStore;

	/**
	 * Cached status of this store.
	 */
	protected Boolean isSet = null;

	// ======================================================================
	//
	// COUNTERS
	//
	// ======================================================================

	/**
	 * Number of times {@code get()} is called.
	 */
	private int getCount = 0;

	/**
	 * Number of times {@code put()} is called.
	 */
	private int putCount = 0;

	// ======================================================================
	//
	// TIME CONSUMPTION
	//
	// ======================================================================

	/**
	 * Milliseconds spent on operations.
	 */
	private long timeConsumption = 0;

	/**
	 * Milliseconds spent on {@code get()} operations.
	 */
	private long getTimeConsumption = 0;

	/**
	 * Milliseconds spent on {@code put()} operations.
	 */
	private long putTimeConsumption = 0;

	/**
	 * Constructor to create memory store
	 *
	 * @param solver     associated Green solver
	 * @param properties properties used to construct the store
	 */
	public MemStore(Green solver, Properties properties) {
		super(solver);
		redisStore = new RedisStore(solver, "localhost", 6379);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see za.ac.sun.cs.green.store.Store#report(za.ac.sun.cs.green.util.Reporter)
	 */
	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("getCount", getCount);
		reporter.report("putCount", putCount);
		reporter.report("timeConsumption", timeConsumption);
		reporter.report("  getTimeConsumption", getTimeConsumption);
		reporter.report("  putTimeConsumption", putTimeConsumption);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see za.ac.sun.cs.green.store.Store#get(java.lang.String)
	 */
	@Override
	public synchronized Object get(String key) {
		long startTime = System.currentTimeMillis();
		getCount++;
		Object s = db.get(key);
		if (s == null) {
			// Greedy approach:
			// if the solution is not in the in-memory cache,
			// look for it in redis (persistent store)
			// and add to cache
			if (redisStore.isSet()) {
				s = redisStore.get(key);
				if (s != null) {
					db.put(key, s);
				}
			}
		}
		getTimeConsumption += System.currentTimeMillis() - startTime;
		timeConsumption += System.currentTimeMillis() - startTime;
		return s;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see za.ac.sun.cs.green.store.Store#put(java.lang.String,
	 * java.io.Serializable)
	 */
	@Override
	public synchronized void put(String key, Serializable value) {
		long startTime = System.currentTimeMillis();
		putCount++;
		// Unnecessary to convert to Base64 string
		db.put(key, value);
		putTimeConsumption += System.currentTimeMillis() - startTime;
		timeConsumption += System.currentTimeMillis() - startTime;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see za.ac.sun.cs.green.store.Store#keySet()
	 */
	@Override
	public Set<String> keySet() {
		if (db.keySet().isEmpty()) {
			if (redisStore.isSet()) {
				return redisStore.keySet();
			} else {
				return Collections.emptySet();
			}
		} else {
			return db.keySet();
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see za.ac.sun.cs.green.store.Store#flushAll()
	 */
	@Override
	public void flushAll() {
		long startTime = System.currentTimeMillis();
		flushAllToRedis();
		timeConsumption += System.currentTimeMillis() - startTime;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see za.ac.sun.cs.green.store.Store#clear()
	 */
	@Override
	public void clear() {
		long startTime = System.currentTimeMillis();
		db.clear();
		if (redisStore.isSet()) {
			redisStore.clear();
		}
		timeConsumption += System.currentTimeMillis() - startTime;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see za.ac.sun.cs.green.store.Store#isSet()
	 */
	@Override
	public boolean isSet() {
		if (isSet == null) {
			try {
				db.get("foo");
				isSet = true;
			} catch (Exception e) {
				isSet = false;
			}
		}
		return isSet;
	}

	/**
	 * Write all of the entries in the in-memory cache to the redis store.
	 */
	protected void flushAllToRedis() {
		if (redisStore.isSet()) {
			db.forEach((k, v) -> redisStore.put(k, (Serializable) v));
		}
	}

}
