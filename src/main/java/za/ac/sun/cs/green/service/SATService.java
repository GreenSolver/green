package za.ac.sun.cs.green.service;

import java.util.Set;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.util.Reporter;

public abstract class SATService extends BasicService {

	private static final String SERVICE_KEY = "SAT:";

	private int invocationCount = 0;

	protected int cacheHitCount = 0;
	protected int satHitCount = 0;
	protected int unsatHitCount = 0;

	protected int cacheMissCount = 0;
	protected int satMissCount = 0;
	protected int unsatMissCount = 0;

	private long timeConsumption = 0;
	protected long storageTimeConsumption = 0;
	private long keyTime = 0;
	private long moreTime = 0;

	protected int satCount = 0;
	protected int unsatCount = 0;

	public SATService(Green solver) {
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
		reporter.report("time to get Key", keyTime);
		reporter.report("outside Redis Time incl keyime", moreTime);
	}

	@Override
	public Object allChildrenDone(Instance instance, Object result) {
		return instance.getData(getClass());
	}

	@Override
	public Set<Instance> processRequest(Instance instance) {
		Boolean result = (Boolean) instance.getData(getClass());
		if (result == null) {
			result = solve0(instance);
			if (result != null) {
				instance.setData(getClass(), result);
			}
		}
//        assert result != null;
		if (result) {
			satCount++;
		} else {
			unsatCount++;
		}
		return null;
	}

	private Boolean solve0(Instance instance) {
		invocationCount++;
		long start = System.currentTimeMillis();
//		String key = SERVICE_KEY + instance.getFullExpression().getString();
		String key = SERVICE_KEY + instance.getFullExpression().toString();
		keyTime += (System.currentTimeMillis() - start);
		Boolean result = store.getBoolean(key);

		if (result == null) {
			cacheMissCount++;
			result = solve1(instance);
			if (result != null) {
				if (result) {
					satMissCount++;
				} else {
					unsatMissCount++;
				}
				store.put(key, result);
			}
		} else {
			cacheHitCount++;
			if (result) {
				satHitCount++;
			} else {
				unsatHitCount++;
			}
		}
		moreTime += (System.currentTimeMillis() - start);
		return result;
	}

	private Boolean solve1(Instance instance) {
		long startTime = System.currentTimeMillis();
		Boolean result = solve(instance);
		timeConsumption += System.currentTimeMillis() - startTime;
		return result;
	}

	protected abstract Boolean solve(Instance instance);

}
