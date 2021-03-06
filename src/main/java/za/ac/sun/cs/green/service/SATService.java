/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service;

import java.util.Set;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Ancestor of all SAT services. These services are expected to, at the least,
 * return a {@code Boolean} result to indicate whether the expression given in
 * the {@link Instance} is satisfiable or not. The service might also return
 * {@code null} if it could not determine the answer.
 */
public abstract class SATService extends BasicService {

	/**
	 * Key prefix used for the store (=cache).
	 */
	public static final String SERVICE_KEY = "SAT:";

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
	 */
	protected int satCount = 0;

	/**
	 * Number of UNSAT answers returned.
	 */
	protected int unsatCount = 0;

	/**
	 * Number of no-answers returned.
	 */
	protected int noAnswerCount = 0;

	/**
	 * Number of times the answer was found in the store.
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
	 * Milliseconds spent to process requests that return no result.
	 */
	protected long noAnswerTimeConsumption = 0;

	/**
	 * Milliseconds spent to compute SAT/UNSAT, including store lookups.
	 */
	protected long innerTimeConsumption = 0;

	/**
	 * Milliseconds spent to compute SAT/UNSAT, excluding store lookups.
	 */
	protected long solveTimeConsumption = 0;

	/**
	 * Milliseconds spent on computing store keys.
	 */
	protected long keyTimeConsumption = 0;

	// ======================================================================
	//
	// CONSTRUCTOR & METHODS
	//
	// ======================================================================

	/**
	 * Construct an instance of a SAT service.
	 *
	 * @param solver associated Green solver
	 */
	public SATService(Green solver) {
		super(solver);
	}

	/**
	 * Report the statistics gathered.
	 *
	 * @param reporter
	 *                 the mechanism through which reporting is done
	 *
	 * @see za.ac.sun.cs.green.service.BasicService#report(za.ac.sun.cs.green.util.Reporter)
	 */
	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("invocationCount", invocationCount);
		reporter.report("  satCount", satCount);
		reporter.report("  unsatCount", unsatCount);
		reporter.report("  noAnswerCount", noAnswerCount);
		reporter.report("cacheHitCount", cacheHitCount);
		reporter.report("  modelHitCount", satHitCount);
		reporter.report("  unsatHitCount", unsatHitCount);
		reporter.report("cacheMissCount", cacheMissCount);
		reporter.report("  modelMissCount", satMissCount);
		reporter.report("  unsatMissCount", unsatMissCount);
		reporter.report("serviceTimeConsumption", serviceTimeConsumption);
		reporter.report("  satTimeConsumption", satTimeConsumption);
		reporter.report("  unsatTimeConsumption", unsatTimeConsumption);
		reporter.report("  noAnswerTimeConsumption", noAnswerTimeConsumption);
		reporter.report("innerTimeConsumption", innerTimeConsumption);
		reporter.report("solveTimeConsumption", solveTimeConsumption);
		reporter.report("keyTimeConsumption", keyTimeConsumption);
		super.report(reporter);
	}

	/**
	 * Process an incoming request. This checks if the instance contains satellite
	 * data for the solution, and, if not, solves the instance by invoking
	 * {@link #solve0(Instance)}, and sets the satellite data itself.
	 * 
	 * Because this is a leaf method (and is not expected to delegate the request),
	 * it always returns {@code null}.
	 *
	 * @param instance
	 *                 problem to solve
	 * @return always {@code null}
	 *
	 * @see za.ac.sun.cs.green.service.BasicService#processRequest(za.ac.sun.cs.green.Instance)
	 */
	@Override
	public Set<Instance> processRequest(Instance instance) {
		long startTime = System.currentTimeMillis();
		invocationCount++;
		Object result = instance.getData(getClass());
		if (result == null) {
			result = solve0(instance);
			if (result != null) {
				instance.setData(getClass(), result);
			}
		}
		if (result instanceof Boolean) {
			if ((Boolean) result) {
				satCount++;
				satTimeConsumption += System.currentTimeMillis() - startTime;
			} else {
				unsatCount++;
				unsatTimeConsumption += System.currentTimeMillis() - startTime;
			}
		} else {
			noAnswerCount++;
			noAnswerTimeConsumption += System.currentTimeMillis() - startTime;
		}
		serviceTimeConsumption += System.currentTimeMillis() - startTime;
		return null;
	}

	/**
	 * Solve a Green instance: in this service, this means that its SAT/UNSAT status
	 * is computed. This first-level routine first checks if the result is available
	 * in the store. If so, it is returned. Otherwise, it is computed.
	 * <p>
	 * Note that some subclasses modify this behaviour.
	 *
	 * @param instance
	 *                 problem to solve
	 * @return the result of the computation: {@code true} mean SAT, {@code false}
	 *         mean UNSAT
	 */
	protected Boolean solve0(Instance instance) {
		long startTime = System.currentTimeMillis();
		String key = SERVICE_KEY + instance.getFullExpression().toString();
		keyTimeConsumption += System.currentTimeMillis() - startTime;
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
		innerTimeConsumption += System.currentTimeMillis() - startTime;
		return result;
	}

	/**
	 * Solve a Green instance for which the answer was not found in the store. If
	 * concurrent computation is used, the answer may appear in the store after this
	 * method is invoked but before it starts its execution. Since the answer is
	 * deterministic, this should not cause problems.
	 *
	 * @param instance
	 *                 problem to solve
	 * @return the result of the computation: {@code true} mean SAT, {@code false}
	 *         mean UNSAT
	 */
	protected Boolean solve1(Instance instance) {
		long startTime = System.currentTimeMillis();
		Boolean result = solve(instance);
		solveTimeConsumption += System.currentTimeMillis() - startTime;
		return result;
	}

	/**
	 * Abstract method that does the actual work to solve a Green instance.
	 *
	 * @param instance
	 *                 problem to solve
	 * @return the result of the computation: {@code true} mean SAT, {@code false}
	 *         mean UNSAT
	 */
	protected abstract Boolean solve(Instance instance);

	/**
	 * Handle the completion of a request by returning the solution stored inside
	 * the satellite data of the GREEN problem.
	 *
	 * @param instance
	 *                 original problem to solve
	 * @param result
	 *                 result from subservices (assumed to be {@code null}
	 * @return the result of the computation: {@code true} mean SAT, {@code false}
	 *         mean UNSAT
	 *
	 * @see za.ac.sun.cs.green.service.BasicService#allChildrenDone(za.ac.sun.cs.green.Instance,
	 *      java.lang.Object)
	 */
	@Override
	public Object allChildrenDone(Instance instance, Object result) {
		return instance.getData(getClass());
	}

	/**
	 * Perform some consistency checks.
	 *
	 * @see za.ac.sun.cs.green.service.BasicService#shutdown()
	 */
	@Override
	public void shutdown() {
		assert (invocationCount == satCount + unsatCount + noAnswerCount);
		assert (invocationCount == cacheHitCount + cacheMissCount);
		assert (satCount == satHitCount + satMissCount);
		assert (unsatCount == unsatHitCount + unsatMissCount);
		super.shutdown();
	}

}
