/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.factorizer;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Service;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.service.BasicService;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Parent of all factorizers.
 */
public class FactorizerService extends BasicService {

	/**
	 * Satellite data key for unresolved factors.
	 */
	public static final String UNSOLVED_FACTORS = "FACTORS_UNSOLVED";

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
	 * Number of constraint that have been factorized.
	 */
	protected int constraintsFactorizedCount = 0;

	/**
	 * Number of factors computed.
	 */
	protected int factorCount = 0;

	// ======================================================================
	//
	// TIME CONSUMPTION
	//
	// ======================================================================

	/**
	 * Milliseconds spent to process requests.
	 */
	protected long serviceTimeConsumption = 0;

	// ======================================================================
	//
	// FIELDS
	//
	// ======================================================================

	protected final Factorizer factorizer;

	// ======================================================================
	//
	// CONSTRUCTOR & METHODS
	//
	// ======================================================================

	/**
	 * Constructor for the factorizer service.
	 * 
	 * @param solver the {@link Green} solver this service will be added to
	 */
	public FactorizerService(Green solver) {
		super(solver);
		factorizer = new Factorizer(log);
	}

	/**
	 * Report the statistics gathered during the execution of this service.
	 *
	 * @param reporter the mechanism through which reporting is done
	 *
	 * @see za.ac.sun.cs.green.service.BasicService#report(za.ac.sun.cs.green.util.Reporter)
	 */
	@Override
	public void report(Reporter reporter) {
		factorizer.report(reporter);
		reporter.setContext(getClass().getSimpleName());
		reporter.report("invocationCount", invocationCount);
		reporter.report("  constraintsFactorizedCount", constraintsFactorizedCount);
		reporter.report("  factorCount", factorCount);
		reporter.report("serviceTimeConsumption", serviceTimeConsumption);
		super.report(reporter);
	}

	/**
	 * Factorize an instance as requested.
	 *
	 * @param instance the instance to factorize
	 * @return set of factors as instances
	 * 
	 * @see za.ac.sun.cs.green.service.BasicService#processRequest(za.ac.sun.cs.green.Instance)
	 */
	@Override
	public Set<Instance> processRequest(Instance instance) {
		long startTime = System.currentTimeMillis();
		invocationCount++;
		@SuppressWarnings("unchecked")
		Set<Instance> result = (Set<Instance>) instance.getData(getClass());
		if (result == null) {
			result = processRequest0(instance);
			instance.setData(getClass(), result);
		}
		serviceTimeConsumption += (System.currentTimeMillis() - startTime);
		return result;
	}

	/**
	 * Internal routine for computing the factors after the required result was not
	 * found in the instance satellite data.
	 *
	 * @param instance the instance to factorize
	 * @return set of factors as instances
	 */
	protected Set<Instance> processRequest0(Instance instance) {
		Set<Expression> factors = factorizer.factorize(instance.getFullExpression());
		Set<Instance> result = new HashSet<>();
		for (Expression factor : factors) {
			result.add(new Instance(getSolver(), instance.getSource(), null, factor));
		}
		result = Collections.unmodifiableSet(result);
		instance.setData(UNSOLVED_FACTORS, new HashSet<>(result));
		factorCount += factors.size();
		return result;
	}

	/**
	 * Process a single result (out of potentially many). At this level, this method
	 * simply records that the result has been solved. Once all outstanding result
	 * has been solved, the final result is returned. Otherwise, {@code null} is
	 * returned to signal to the task manager that the computation should continue.
	 * It is expected that subclasses of this class many implement additional logic.
	 *
	 * @param instance    input instance
	 * @param subservice  subservice (= child service) that computed a result
	 * @param subinstance subinstance which this service passed to the subservice
	 * @param result      result return by the sub-service
	 * @return a new (intermediary) result
	 *
	 * @see za.ac.sun.cs.green.service.BasicService#childDone(za.ac.sun.cs.green.Instance,
	 *      za.ac.sun.cs.green.Service, za.ac.sun.cs.green.Instance,
	 *      java.lang.Object)
	 */
	@Override
	public Object childDone(Instance instance, Service subservice, Instance subinstance, Object result) {
		@SuppressWarnings("unchecked")
		Set<Instance> unsolved = (Set<Instance>) instance.getData(UNSOLVED_FACTORS);
		if (unsolved.contains(subinstance)) {
			result = handleNewChild(instance, subservice, subinstance, result);
			unsolved.remove(subinstance);
			instance.setData(UNSOLVED_FACTORS, unsolved);
			// Return true if no more unsolved factors; else return null to carry on the
			// computation
			return (unsolved.isEmpty()) ? result : null;
		} else {
			// We have already solved this subinstance; return null to carry on the
			// computation or result if there is no more work outstanding
			return (unsolved.isEmpty()) ? result : null;
		}
	}

	/**
	 * Perform additional processing for intermediate results. This default simply
	 * returns the result returned from the child service.
	 *
	 * @param instance    input instance
	 * @param subservice  subservice (= child service) that computed a result
	 * @param subinstance subinstance which this service passed to the subservice
	 * @param result      result return by the sub-service
	 * @return a new (intermediary) result
	 */
	protected Object handleNewChild(Instance instance, Service subservice, Instance subinstance, Object result) {
		return result;
	}

	/**
	 * Check there are unsolved factors and a {@code null} result is returned and,
	 * if so, issue a warning. This is perhaps an error, but it may also indicate
	 * that the Green pipeline is not able to handle an instance.
	 *
	 * @param instance input instance
	 * @param result   result computed so far by this service
	 * @return final result
	 * 
	 * @see za.ac.sun.cs.green.service.BasicService#allChildrenDone(za.ac.sun.cs.green.Instance,
	 *      java.lang.Object)
	 */
	@Override
	public Object allChildrenDone(Instance instance, Object result) {
		@SuppressWarnings("unchecked")
		Set<Instance> unsolved = (Set<Instance>) instance.getData(UNSOLVED_FACTORS);
		if (!unsolved.isEmpty() && (result == null)) {
			log.warn("unsolved factors but result is null");
		}
		return super.allChildrenDone(instance, result);
	}

}
