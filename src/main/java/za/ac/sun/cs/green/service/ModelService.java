package za.ac.sun.cs.green.service;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.util.Reporter;

public abstract class ModelService extends BasicService {

	private static final String SERVICE_KEY = "MODEL:";

	private int invocationCount = 0;

	protected int cacheHitCount = 0;
	protected int satHitCount = 0;
	protected int unsatHitCount = 0;

	protected int cacheMissCount = 0;
	protected int satMissCount = 0;
	protected int unsatMissCount = 0;

	private long timeConsumption = 0;
	protected long storageTimeConsumption = 0;

	protected int satCount = 0;
	protected int unsatCount = 0;

	public ModelService(Green solver) {
		super(solver);
	}

	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("invocationCount", invocationCount);
		reporter.report("cacheHitCount", cacheHitCount);
		reporter.report("satCacheHitCount", satHitCount);
		reporter.report("unsatCacheHitCount", unsatHitCount);
		reporter.report("cacheMissCount", cacheMissCount);
		reporter.report("satCacheMissCount", satMissCount);
		reporter.report("unsatCacheMissCount", unsatMissCount);
		reporter.report("timeConsumption", timeConsumption);
		reporter.report("storageTimeConsumption", storageTimeConsumption);
		reporter.report("satQueries", satCount);
		reporter.report("unssatQueries", unsatCount);
	}

	@Override
	public Object allChildrenDone(Instance instance, Object result) {
		return instance.getData(getClass());
	}

	@Override
	public Set<Instance> processRequest(Instance instance) {
		@SuppressWarnings("unchecked")
		Map<Variable, Object> result = (Map<Variable, Object>) instance.getData(getClass());
		if (result == null) {
			result = solve0(instance);
			if (result != null) {
				instance.setData(getClass(), result);
			}
		}
		return null;
	}

	private Map<Variable, Object> solve0(Instance instance) {
		invocationCount++;
//		String key = SERVICE_KEY + instance.getFullExpression().getString();
		String key = SERVICE_KEY + instance.getFullExpression().toString();
		long tmpConsumption = 0L;
		long start = System.currentTimeMillis();
		@SuppressWarnings("unchecked")
		HashMap<Variable, Object> result = (HashMap<Variable, Object>) store.get(key);
		if (result == null) {
			cacheMissCount++;
			long startTime = System.currentTimeMillis();
			result = solve1(instance);
			timeConsumption += (System.currentTimeMillis() - startTime);
			tmpConsumption = System.currentTimeMillis() - startTime;
			if (result != null) {
				satMissCount++;
				store.put(key, result);
			} else {
				unsatMissCount++;
			}
		} else {
			satHitCount++;
			cacheHitCount++;
		}
		storageTimeConsumption += ((System.currentTimeMillis() - start) - tmpConsumption);
		return result;
	}

	private HashMap<Variable, Object> solve1(Instance instance) {
		HashMap<Variable, Object> result = (HashMap<Variable, Object>) model(instance);
		return result; // change this!
	}

	protected abstract Map<Variable, Object> model(Instance instance);

}
