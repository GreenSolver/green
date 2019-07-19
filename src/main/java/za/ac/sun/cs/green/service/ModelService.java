/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service;

import java.io.Serializable;
import java.util.Map;
import java.util.Set;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.service.ModelCoreService.ModelCore;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Ancestor of all services that return a model if an instance is satisfiable.
 * These services are expected to return a {@link Model} object as a result to
 * indicate if the expression given in the {@link Instance} is satisfiable. The
 * service might also return {@code null} if it could not determine the answer.
 */
public abstract class ModelService extends BasicService {

	/**
	 * Key prefix used for the store (=cache) for models.
	 */
	public static final String SERVICE_KEY = "MODEL:";

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
	 * Number of models returned.
	 */
	protected int modelCount = 0;

	/**
	 * Number of times no model is returned.
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
	 * Number of times a model was found in the store.
	 */
	protected int modelHitCount = 0;

	/**
	 * Number of times no model was found in the store.
	 */
	protected int unsatHitCount = 0;

	/**
	 * Number of times an answer was NOT found in the store.
	 */
	protected int cacheMissCount = 0;

	/**
	 * Number of times an answer was NOT found in the store and a model was found.
	 */
	protected int modelMissCount = 0;

	/**
	 * Number of times an answer was NOT found in the store and no model was found
	 * either.
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
	 * Milliseconds spent to process requests that eventually produce a model.
	 */
	protected long modelTimeConsumption = 0;

	/**
	 * Milliseconds spent to process requests that eventually produce no model.
	 */
	protected long unsatTimeConsumption = 0;

	/**
	 * Milliseconds spent to process requests that do not produce an answer.
	 */
	protected long noAnswerTimeConsumption = 0;

	/**
	 * Milliseconds spent to compute models, including store lookups.
	 */
	protected long solveTimeConsumption = 0;

	/**
	 * Milliseconds spent to compute models, excluding store lookups.
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
	 * Construct an instance of a model service.
	 *
	 * @param solver
	 *               associated Green solver
	 */
	public ModelService(Green solver) {
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
		reporter.report("  modelCount", modelCount);
		reporter.report("  unsatCount", unsatCount);
		reporter.report("  noAnswerCount", noAnswerCount);
		reporter.report("cacheHitCount", cacheHitCount);
		reporter.report("  modelHitCount", modelHitCount);
		reporter.report("  unsatHitCount", unsatHitCount);
		reporter.report("cacheMissCount", cacheMissCount);
		reporter.report("  modelMissCount", modelMissCount);
		reporter.report("  noModelMissCount", unsatMissCount);
		reporter.report("serviceTimeConsumption", serviceTimeConsumption);
		reporter.report("  modelTimeConsumption", modelTimeConsumption);
		reporter.report("  unsatTimeConsumption", unsatTimeConsumption);
		reporter.report("  noAnswerTimeConsumption", noAnswerTimeConsumption);
		reporter.report("solveTimeConsumption", solveTimeConsumption);
		reporter.report("innerTimeConsumption", innerTimeConsumption);
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
		if (result instanceof Model) {
			if (((Model) result).isSat()) {
				modelCount++;
				modelTimeConsumption += System.currentTimeMillis() - startTime;
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
	 * is computed and, if it is SAT, a model is returned. This first-level routine
	 * first checks if the result is available in the store. If so, it is returned.
	 * Otherwise, it is computed.
	 * <p>
	 * Note that some subclasses modify this behaviour.
	 *
	 * @param instance
	 *                 problem to solve
	 * @return the result of the computation as a {@link Model}
	 */
	protected Model solve0(Instance instance) {
		long startTime = System.currentTimeMillis();
		String key = SERVICE_KEY + instance.getFullExpression().toString();
		keyTimeConsumption += System.currentTimeMillis() - startTime;
		Model result = (Model) store.get(key);
		if (result == null) {
			cacheMissCount++;
			result = solve1(instance);
			if (result != null) {
				if (result.isSat()) {
					modelMissCount++;
				} else {
					unsatMissCount++;
				}
				store.put(key, result);
			}
		} else {
			cacheHitCount++;
			if (result.isSat()) {
				modelHitCount++;
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
	 * @return the result of the computation as a {@link Model}
	 */
	protected Model solve1(Instance instance) {
		long startTime = System.currentTimeMillis();
		Model result = model(instance);
		solveTimeConsumption += System.currentTimeMillis() - startTime;
		return result;
	}

	/**
	 * Abstract method that does the actual work to solve a Green instance.
	 *
	 * @param instance
	 *                 problem to solve
	 * @return result of the computation as a {@link Model}
	 */
	protected abstract Model model(Instance instance);

	/**
	 * Handle the completion of a request by returning the solution stored inside
	 * the satellite data of the GREEN problem.
	 *
	 * @param instance
	 *                 original problem to solve
	 * @param result
	 *                 result from subservices (assumed to be {@code null}
	 * @return number of satisfying models as a {@link ModelCore}
	 *
	 * @see za.ac.sun.cs.green.service.BasicService#allChildrenDone(za.ac.sun.cs.green.Instance,
	 *      java.lang.Object)
	 */
	@Override
	public Object allChildrenDone(Instance instance, Object result) {
		return instance.getData(getClass());
	}

	// ======================================================================
	//
	// ENCAPSULATION OF A MODEL
	//
	// ======================================================================

	/**
	 * Encapsulation of a model. It is expected that all implementing services use
	 * this object.
	 */
	public static class Model implements Serializable {

		/**
		 * Required for serialization.
		 */
		private static final long serialVersionUID = 6279584222682123539L;

		/**
		 * Does this result represent a satisfying solution?
		 */
		private final boolean isSat;

		/**
		 * The model, if {@link #isSat} is {@code true}. Otherwise, {@code null}.
		 */
		private final Map<Variable, Constant> model;

		/**
		 * Create an instance of a model / core.
		 *
		 * @param isSat
		 *              is this solution satisfying?
		 * @param model
		 *              the model for this solution (or {@code null})
		 */
		public Model(final boolean isSat, final Map<Variable, Constant> model) {
			this.isSat = isSat;
			this.model = model;
		}

		/**
		 * Return the satisfying flag for this solution.
		 *
		 * @return {@code true}/{@code false} to indicate satisfiability
		 */
		public boolean isSat() {
			return isSat;
		}

		/**
		 * Return the satisfying model or {@code null}.
		 *
		 * @return the satisfying model or {@code null}
		 */
		public Map<Variable, Constant> getModel() {
			return model;
		}

	}

}
