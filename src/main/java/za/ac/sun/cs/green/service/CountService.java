/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service;

import java.util.Set;

import org.apfloat.Apint;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Ancestor of all counting services. These services are expected to, at the
 * least, return a {@code Apint} result to indicate the number of models for the
 * expression in an {@link Instance}. This number should be 0 if and only if the
 * expression is unsatisfiable. The service might also return {@code null} if it
 * could not determine the answer.
 */
public abstract class CountService extends BasicService {

	/**
	 * Key prefix used for the store (=cache).
	 */
	private static final String SERVICE_KEY = "COUNT:";

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
	 * Number of times the answer was found in the store.
	 */
	protected int cacheHitCount = 0;

	/**
	 * Number of times an answer was NOT found in the store.
	 */
	protected int cacheMissCount = 0;

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
	 * Milliseconds spent to compute models/cores, including store lookups.
	 */
	protected long solveTimeConsumption = 0;

	/**
	 * Milliseconds spent to compute models/cores, excluding store lookups.
	 */
	protected long innerTimeConsumption = 0;

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
	 * Construct an instance of a counting service.
	 *
	 * @param solver
	 *               associated Green solver
	 */
	public CountService(Green solver) {
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
		reporter.report("  cacheHitCount", cacheHitCount);
		reporter.report("  cacheMissCount", cacheMissCount);
		reporter.report("serviceTimeConsumption", serviceTimeConsumption);
		reporter.report("solveTimeConsumption", solveTimeConsumption);
		reporter.report("innerTimeConsumption", innerTimeConsumption);
		reporter.report("keyTimeConsumption", keyTimeConsumption);
	}

	/**
	 * Process an incoming request. This checks if the instance contains satellite
	 * data for the solution, and, if not, solves the instance by invoking
	 * {@link #solve0(Instance)}, and sets the satellite data itself.
	 * 
	 * Because this is a leaf method (and is not expected to delegate the request),
	 * it always returns {@code null}.
	 *
	 * @param instance problem to solve
	 * @return number of satisfying models for the problem
	 *
	 * @see za.ac.sun.cs.green.service.BasicService#processRequest(za.ac.sun.cs.green.Instance)
	 */
	@Override
	public Set<Instance> processRequest(Instance instance) {
		long startTime = System.currentTimeMillis();
		invocationCount++;
		Object result = instance.getData(getClass());
		if (!(result instanceof Apint)) {
			result = solve0(instance);
			if (result != null) {
				instance.setData(getClass(), result);
			}
		}
		serviceTimeConsumption += System.currentTimeMillis() - startTime;
		return null;
	}

	/**
	 * Handle the request to count the number of satisfying solutions for a GREEN
	 * problem. The first step is to check if the solution can be found in the
	 * store. It not, the method invokes {@link #solve1(Instance)} to compute the
	 * answer, stores it in the store, and returns it.
	 *
	 * @param instance
	 *                 problem to solve
	 * @return number of satisfying models for the problem
	 */
	private Apint solve0(Instance instance) {
		long startTime = System.currentTimeMillis();
		String key = SERVICE_KEY + instance.getFullExpression().toString();
		keyTimeConsumption += System.currentTimeMillis() - startTime;
		Apint result = store.getApfloatInteger(key);
		if (result == null) {
			cacheMissCount++;
			result = solve1(instance);
			if (result != null) {
				store.put(key, result);
			}
		} else {
			cacheHitCount++;
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
	 * @param instance problem to solve
	 * @return number of satisfying models for the problem
	 */
	protected Apint solve1(Instance instance) {
		long startTime = System.currentTimeMillis();
		Apint result = count(instance);
		solveTimeConsumption += System.currentTimeMillis() - startTime;
		return result;
	}

	/**
	 * Abstract method that does the actual work of counting the number of
	 * satisfying models for a given GREEN problem.
	 *
	 * @param instance
	 *                 problem to solve
	 * @return number of satisfying models for the problem
	 */
	protected abstract Apint count(Instance instance);

	/**
	 * Handle the completion of a request by returning the solution stored inside
	 * the satellite data of the GREEN problem.
	 *
	 * @param instance
	 *                 original problem to solve
	 * @param result
	 *                 result from subservices (assumed to be {@code null}
	 * @return number of satisfying models as an {@link Apint}
	 *
	 * @see za.ac.sun.cs.green.service.BasicService#allChildrenDone(za.ac.sun.cs.green.Instance,
	 *      java.lang.Object)
	 */
	@Override
	public Object allChildrenDone(Instance instance, Object result) {
		return instance.getData(getClass());
	}

}
