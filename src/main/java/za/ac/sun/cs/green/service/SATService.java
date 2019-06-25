package za.ac.sun.cs.green.service;

import java.util.Set;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Ancestor of all SAT services. These services are expected to, at the least,
 * return a Boolean result to indicate whether the expression given in the
 * {@link Instance is satisfiable or not.} The service might also return
 * {@code null} if it could not determine the answer.
 */
public abstract class SATService extends BasicService {

	/**
	 * Key prefix used for the store (=cache).
	 */
	protected static final String SERVICE_KEY = "SAT:";

	// ======================================================================
	//
	// COUNTERS
	//
	// ======================================================================

	/**
	 * Number of times this service has been invoked.
	 */
	protected int invocationCount = 0;

	/**
	 * Number of SAT answers returned.
	 * 
	 * {@link #satCount} + {@link #unsatCount} <= {@link #invocationCount}
	 * 
	 * {@link #satHitCount} + {@link #satMissCount} = {@link #satCount}
	 */
	protected int satCount = 0;

	/**
	 * Number of UNSAT answers returned.
	 * 
	 * {@link #unsatHitCount} + {@link #unsatMissCount} = {@link #unsatCount}
	 */
	protected int unsatCount = 0;

	/**
	 * Number of times the answer was found in the store.
	 * 
	 * {@link #cacheHitCount} + {@link #cacheMissCount} <= {@link #invocationCount}
	 */
	protected int cacheHitCount = 0;

	/**
	 * Number of times a SAT answer was found in the store.
	 */
	protected int satHitCount = 0;

	/**
	 * Number of times an UNSAT answer was found in the store.
	 */
	protected int unsatHitCount = 0;

	/**
	 * Number of times an answer was NOT found in the store.
	 */
	protected int cacheMissCount = 0;

	/**
	 * Number of times an answer was NOT found in the store and calculated to be
	 * SAT.
	 */
	protected int satMissCount = 0;

	/**
	 * Number of times an answer was NOT found in the store and calculated to be
	 * UNSAT.
	 */
	protected int unsatMissCount = 0;

	// ======================================================================
	//
	// TIME CONSUMPTION
	//
	// ======================================================================

	/**
	 * Milliseconds spent to process requests.
	 */
	protected long serviceTimeConsumption = 0;
	
	/**
	 * Milliseconds spent to process requests that are SAT.
	 */
	protected long satTimeConsumption = 0;
	
	/**
	 * Milliseconds spent to process requests that are UNSAT.
	 */
	protected long unsatTimeConsumption = 0;
	
	/**
	 * Milliseconds spent to compute SAT/UNSAT, including store lookups.
	 */
	protected long fullTimeConsumption = 0;
	
	/**
	 * Milliseconds spent to compute SAT/UNSAT, excluding store lookups.
	 */
	protected long innerTimeConsumption = 0;

	/**
	 * Milliseconds spent on computing store keys.
	 */
	protected long keyTimeConsumption = 0;

	/**
	 * Construct an instance of a SAT service.
	 * 
	 * @param solver associated Green solver
	 */
	public SATService(Green solver) {
		super(solver);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see za.ac.sun.cs.green.service.BasicService#report(za.ac.sun.cs.green.util.
	 * Reporter)
	 */
	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("invocationCount", invocationCount);
		reporter.report("satCount", satCount);
		reporter.report("unsatCount", unsatCount);
		reporter.report("cacheHitCount", cacheHitCount);
		reporter.report("satHitCount", satHitCount);
		reporter.report("unsatHitCount", unsatHitCount);
		reporter.report("cacheMissCount", cacheMissCount);
		reporter.report("satMissCount", satMissCount);
		reporter.report("unsatMissCount", unsatMissCount);
		reporter.report("serviceTimeConsumption", serviceTimeConsumption);
		reporter.report("satTimeConsumption", satTimeConsumption);
		reporter.report("unsatTimeConsumption", unsatTimeConsumption);
		reporter.report("fullTimeConsumption", fullTimeConsumption);
		reporter.report("innerTimeConsumption", innerTimeConsumption);
		reporter.report("keyTimeConsumption", keyTimeConsumption);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * za.ac.sun.cs.green.service.BasicService#allChildrenDone(za.ac.sun.cs.green.
	 * Instance, java.lang.Object)
	 */
	@Override
	public Object allChildrenDone(Instance instance, Object result) {
		return instance.getData(getClass());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * za.ac.sun.cs.green.service.BasicService#processRequest(za.ac.sun.cs.green.
	 * Instance)
	 */
	@Override
	public Set<Instance> processRequest(Instance instance) {
		long startTime = System.currentTimeMillis();
		Object result = instance.getData(getClass());
		if (result == null) {
			result = solve0(instance);
			if (result != null) {
				instance.setData(getClass(), result);
			}
		}
		if ((result != null) && (result instanceof Boolean)) {
			if ((Boolean) result) {
				satCount++;
				satTimeConsumption += (System.currentTimeMillis() - startTime);
			} else {
				unsatCount++;
				unsatTimeConsumption += (System.currentTimeMillis() - startTime);
			}
		}
		serviceTimeConsumption += (System.currentTimeMillis() - startTime);
		return null;
	}

	/**
	 * Solve a Green instance: in this service, this means that its SAT/UNSAT status
	 * is computed. This first-level routine first checks if the result is available
	 * in the store. If so, it is returned. Otherwise, it is computed.
	 * 
	 * Note that some subclasses modify this behaviour.
	 * 
	 * @param instance Green instance to solve
	 * @return the result of the computation: {@code true} mean SAT, {@code false}
	 *         mean UNSAT
	 */
	protected Boolean solve0(Instance instance) {
		long startTime = System.currentTimeMillis();
		invocationCount++;
		String key = SERVICE_KEY + instance.getFullExpression().toString();
		keyTimeConsumption += (System.currentTimeMillis() - startTime);
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
		fullTimeConsumption += (System.currentTimeMillis() - startTime);
		return result;
	}

	/**
	 * Solve a Green instance for which the answer was not found in the store. If
	 * concurrent computation is used, the answer may appear in the store after this
	 * method is invoked but before it starts its execution. Since the answer is
	 * deterministic, this should not cause problems.
	 * 
	 * @param instance Green instance to solve
	 * @return the result of the computation: {@code true} mean SAT, {@code false}
	 *         mean UNSAT
	 */
	protected Boolean solve1(Instance instance) {
		long startTime = System.currentTimeMillis();
		Boolean result = solve(instance);
		innerTimeConsumption += System.currentTimeMillis() - startTime;
		return result;
	}

	/**
	 * Do the actual work to solve a Green instance.
	 *
	 * @param instance
	 * @param instance Green instance to solve
	 * @return the result of the computation: {@code true} mean SAT, {@code false}
	 *         mean UNSAT
	 */
	protected abstract Boolean solve(Instance instance);

}
