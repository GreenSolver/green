package za.ac.sun.cs.green.store.redis;

import java.io.IOException;
import java.io.Serializable;
import java.util.Properties;

import io.lettuce.core.RedisClient;
import io.lettuce.core.api.StatefulRedisConnection;
import io.lettuce.core.api.async.RedisAsyncCommands;
import io.lettuce.core.api.sync.RedisCommands;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.store.BasicStore;
import za.ac.sun.cs.green.util.Configuration;
import za.ac.sun.cs.green.util.Reporter;

/**
 * An implementation of a {@link za.ac.sun.cs.green.store.Store} based on redis (<code>http://www.redis.io</code>).
 * 
 * @author Jaco Geldenhuys <jaco@cs.sun.ac.za>
 */
public class RedisLettuceStore extends BasicStore {

	/**
	 * Representation of the Redis client.
	 */
	private final RedisClient redisClient;

	/**
	 * Connection to the Redis server.
	 */
	private final StatefulRedisConnection<String, String> redisConnection;
	
	/**
	 * Synchronous Redis command channel.
	 */
	private final RedisCommands<String, String> syncCommands;
	
	/**
	 * Asynchronous Redis command channel.
	 */
	private final RedisAsyncCommands<String, String> asyncCommands;
	
	/**
	 * Number of times <code>get(...)</code> was called.
	 */
	private int retrievalCount = 0;

	/**
	 * Number of times <code>put(...)</code> was called.
	 */
	private int insertionCount = 0;

	/**
	 * The default host of the redis server.
	 */
	private final String DEFAULT_REDIS_HOST = "localhost";

	/**
	 * Options passed to the LattE executable.
	 */
	private final int DEFAULT_REDIS_PORT = 6379;
	
	private long timePut = 0;
	private long timeGet = 0;
	
	/**
	 * Constructor to create a default connection to a redis store running on the local computer.
	 */
	public RedisLettuceStore(Green solver, Properties properties) {
		super(solver);
		String h = properties.getProperty("green.redis.host", DEFAULT_REDIS_HOST);
		int p = Configuration.getIntegerProperty(properties, "green.redis.port", DEFAULT_REDIS_PORT);
		redisClient = RedisClient.create("redis://" + h + ":" + p + "/0");
		redisConnection = redisClient.connect();
		syncCommands = redisConnection.sync();
		asyncCommands = redisConnection.async();
	}
	
	/**
	 * Constructor to create a connection to a redis store given the host and the port.
	 * 
	 * @param host the host on which the redis store is running
	 * @param port the port on which the redis store is listening
	 */
	public RedisLettuceStore(Green solver, String host, int port) {
		super(solver);
		redisClient = RedisClient.create("redis://" + host + ":" + port + "/0");
		redisConnection = redisClient.connect();
		syncCommands = redisConnection.sync();
		asyncCommands = redisConnection.async();
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
		try {
			String s = syncCommands.get(key);
			timeGet += (System.currentTimeMillis()-start);
			return (s == null) ? null : fromString(s);
		} catch (IOException x) {
			LOGGER.fatal("io problem", x);
		} catch (ClassNotFoundException x) {
			LOGGER.fatal("class not found problem", x);
		}
		timeGet += (System.currentTimeMillis()-start);
		return null;
	}

	@Override
	public synchronized void put(String key, Serializable value) {
		long start = System.currentTimeMillis();
		insertionCount++;
		try {
			asyncCommands.set(key, toString(value));
		} catch (IOException x) {
			LOGGER.fatal("io problem", x);
		}
		timePut += (System.currentTimeMillis()-start);
	}
	
	public void flushAll() {
  //      long start = System.currentTimeMillis();
		syncCommands.flushall();
    //    timeFlush += (System.currentTimeMillis()-start);
}

}
