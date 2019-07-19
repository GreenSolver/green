package za.ac.sun.cs.green.store.memstore;

import java.io.Serializable;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.store.BasicStore;
import za.ac.sun.cs.green.store.Store;
import za.ac.sun.cs.green.util.Configuration;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Implementation of a {@link BasicStore} that caches its results in memory and
 * falls back on a secondary {@link Store}. When flushing, stored information
 * are written to the secondary store.
 */
public class MemStore extends BasicStore {

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

	/**
	 * Milliseconds spent on flushing to secondary store.
	 */
	protected long flushTimeConsumption = 0;
	
	// ======================================================================
	//
	// FIELDS
	//
	// ======================================================================

	/**
	 * The in-memory cache.
	 */
	protected final Map<String, Object> memoryStore = new HashMap<>();

	/**
	 * The secondary store to fall back on.
	 */
	protected Store secondaryStore;

	// ======================================================================
	//
	// CONSTRUCTOR & METHODS
	//
	// ======================================================================

	/**
	 * Constructor to create an in-memory store.
	 *
	 * @param solver
	 *                   associated Green solver
	 * @param properties
	 *                   properties used to construct the store
	 */
	public MemStore(final Green solver) {
		super(solver);
		secondaryStore = null;
	}

	/**
	 * Constructor to create a named in-memory store.
	 *
	 * @param solver
	 *                   associated Green solver
	 * @param name name of the store
	 * @param properties
	 *                   properties used to construct the store
	 */
	@Override
	public void setName(final String name) {
		secondaryStore = Configuration.loadStore(solver, "green.store." + name + ".secondary");
		super.setName(name);
	}
	
	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("getCount", getCount);
		reporter.report("putCount", putCount);
		reporter.report("storeTimeConsumption", storeTimeConsumption);
		reporter.report("  getTimeConsumption", getTimeConsumption);
		reporter.report("  putTimeConsumption", putTimeConsumption);
		reporter.report("  flushTimeConsumption", flushTimeConsumption);
	}

	/**
	 * Return the value for the key if it is present in the memory store. If not,
	 * check for the key in the secondary store. If found, add the key-value pair to
	 * the memory store and return the value.
	 *
	 * @param key
	 *            the key to use for the lookup
	 * @return the object that is stored with the key or {@code null} if no
	 *         association is found
	 *
	 * @see za.ac.sun.cs.green.store.Store#get(java.lang.String)
	 */
	@Override
	public synchronized Object get(String key) {
		long startTime = System.currentTimeMillis();
		getCount++;
		Object value = memoryStore.get(key);
		if ((value == null) && (secondaryStore != null)) {
			value = secondaryStore.get(key);
			if (value != null) {
				memoryStore.put(key, value);
			}
		}
		getTimeConsumption += System.currentTimeMillis() - startTime;
		storeTimeConsumption += System.currentTimeMillis() - startTime;
		return value;
	}

	@Override
	public synchronized void put(String key, Serializable value) {
		long startTime = System.currentTimeMillis();
		putCount++;
		memoryStore.put(key, value);
		putTimeConsumption += System.currentTimeMillis() - startTime;
		storeTimeConsumption += System.currentTimeMillis() - startTime;
	}

	@Override
	public Set<String> keySet() {
		Set<String> keySet = memoryStore.keySet();
		if (keySet.isEmpty() && (secondaryStore != null)) {
			keySet = secondaryStore.keySet();
		}
		return keySet;
	}

	/**
	 * Write all stored information to the secondary store, if any.  The in-memory store is NOT cleared.
	 *
	 * @see za.ac.sun.cs.green.store.BasicStore#flushAll()
	 */
	@Override
	public void flushAll() {
		long startTime = System.currentTimeMillis();
		if (secondaryStore != null) {
			memoryStore.forEach((k, v) -> secondaryStore.put(k, (Serializable) v));
		}
		flushTimeConsumption += System.currentTimeMillis() - startTime;
		storeTimeConsumption += System.currentTimeMillis() - startTime;
	}

	/**
	 * This operation clears the in-memory store but does not affect the secondary store, if any.
	 *
	 * @see za.ac.sun.cs.green.store.BasicStore#clear()
	 */
	@Override
	public void clear() {
		long startTime = System.currentTimeMillis();
		memoryStore.clear();
		storeTimeConsumption += System.currentTimeMillis() - startTime;
	}

}
