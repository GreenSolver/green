package za.ac.sun.cs.green.store.memstore;

import java.io.IOException;
import java.io.Serializable;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

import redis.clients.jedis.Jedis;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.store.BasicStore;
import za.ac.sun.cs.green.util.Configuration;
import za.ac.sun.cs.green.util.Reporter;

/**
 * An implementation of a {@link za.ac.sun.cs.green.store.Store} based on redis (<code>http://www.redis.io</code>).
 * 
 * @author Jaco Geldenhuys <jaco@cs.sun.ac.za>
 */
public class MemSATStore extends BasicStore {

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
	private Map<String,Boolean> db;
	
	private long timePut = 0;
	private long timeGet = 0;
	
	
	
	/**
	 * Constructor to create memory store
	 */
	public MemSATStore(Green solver, Properties properties) {
		super(solver);
		db = new HashMap<String,Boolean>();
	}
	
	@Override
	public void report(Reporter reporter) {
		reporter.report(getClass().getSimpleName(), "retrievalCount = " + retrievalCount);
		reporter.report(getClass().getSimpleName(), "insertionCount = " + insertionCount);
		reporter.report(getClass().getSimpleName(), "time for get = " + timeGet);
		reporter.report(getClass().getSimpleName(), "iime for put = " + timePut);
	}
	
	@Override
	public synchronized Object get(String key) {
		long start = System.currentTimeMillis();
		retrievalCount++;
		Boolean b = db.get(key);
		timeGet += (System.currentTimeMillis()-start);
		return b;
	}

	@Override
	public synchronized void put(String key, Serializable value) {
		long start = System.currentTimeMillis();
		insertionCount++;
		//try {
			db.put(key, (Boolean)value);
		//} catch (IOException x) {
		//	LOGGER.fatal("io problem", x);
		//}
		timePut += (System.currentTimeMillis()-start);
	}

}
