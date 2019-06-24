package za.ac.sun.cs.green.store.memstore;

import java.io.Serializable;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;
import java.util.Set;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.service.grulia.Entry;
import za.ac.sun.cs.green.store.BasicStore;
import za.ac.sun.cs.green.store.redis.RedisStore;
import za.ac.sun.cs.green.util.Reporter;

/**
 * An implementation of a {@link za.ac.sun.cs.green.store.Store} based on redis
 * (<code>http://www.redis.io</code>).
 *
 * @author Jaco Geldenhuys <jaco@cs.sun.ac.za>
 */
public class MemStore extends BasicStore {

	/**
	 * Number of times <code>get(...)</code> was called.
	 */
	private int retrievalCount = 0;

	/**
	 * Number of times <code>put(...)</code> was called.
	 */
	private int insertionCount = 0;

	/**
	 * The Memory Store
	 *
	 */
	private Map<String, Object> db;
	private RedisStore redisStore;

	private long timePut = 0;
	private long timeGet = 0;
	private long timeConsumption = 0;

	/**
	 * Constructor to create memory store
	 */
	public MemStore(Green solver, Properties properties) {
		super(solver);
		db = new HashMap<String, Object>();
		redisStore = new RedisStore(solver, "localhost", 6379);
	}

	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("retrievalCount", retrievalCount);
		reporter.report("insertionCount", insertionCount);
		reporter.report("timeConsumption", timeConsumption);
		reporter.report("getTime", timeGet);
		reporter.report("putTime", timePut);
	}

	@Override
	public synchronized Object get(String key) {
		long start = System.currentTimeMillis();
		retrievalCount++;
		Object s = db.get(key);
		if (s == null) {
			// Greedy approach:
			// if the solution is not in the memstore,
			// look for it in redis (persistent store)
			// and add to memstore
			if (redisStore.isSet()) {
				s = redisStore.get(key);
				if (s != null) {
					db.put(key, s);
				}
			}
		}
		timeGet += (System.currentTimeMillis() - start);
		timeConsumption += (System.currentTimeMillis() - start);
		return s;
	}

	@Override
	public synchronized void put(String key, Serializable value) {
		long start = System.currentTimeMillis();
		insertionCount++;
		// Unnecessary to convert to Base64 string
		db.put(key, value);
		timePut += (System.currentTimeMillis() - start);
		timeConsumption += (System.currentTimeMillis() - start);
	}

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

	@Override
	public void flushAll() {
		long start = System.currentTimeMillis();
		flushAllToRedis();
		timeConsumption += (System.currentTimeMillis() - start);
	}

	@Override
	public void clear() {
		long start = System.currentTimeMillis();
		db.clear();
		if (redisStore.isSet()) {
			redisStore.clear();
		}
		timeConsumption += (System.currentTimeMillis() - start);
	}

	@Override
	public boolean isSet() {
		try {
			db.get("foo");
			return true;
		} catch (Exception e) {
			return false;
		}
	}

	private void flushAllToRedis() {
		if (redisStore.isSet()) {
			for (String key : db.keySet()) {
				Object e = db.get(key);
				if (e instanceof String) {
					redisStore.put(key, (String) e);
				} else if (e instanceof Boolean) {
					redisStore.put(key, (Boolean) e);
				} else if (e instanceof Entry) {
					redisStore.put(key, (Entry) e);
				} else {
					solver.getLogger().warn("Object not catered for.");
				}
			}
		}
	}

}
