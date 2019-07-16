package za.ac.sun.cs.green.service;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.service.ModelService.Model;
import za.ac.sun.cs.green.util.Reporter;

import java.io.Serializable;
import java.util.Map;
import java.util.Set;

/**
 * Ancestor of all services that return a model if an instance is satisfiable,
 * or a core if it is not. These services are expected to return a
 * {@link ModelCore} object as a result to indicate if the expression given in
 * the {@link Instance} is satisfiable. The service might also return
 * {@code null} if it could not determine the answer.
 */
public abstract class ModelCoreService extends BasicService {

	/**
	 * Key prefix used for model-cores in stores.
	 */
	public static final String SERVICE_KEY = "MODELCORE:";

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
	 * Number of cores returned.
	 */
	protected int coreCount = 0;

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
	 * Number of times a core was found in the store.
	 */
	protected int coreHitCount = 0;

	/**
	 * Number of times an answer was NOT found in the store.
	 */
	protected int cacheMissCount = 0;

	/**
	 * Number of times an answer was NOT found in the store and a model was found.
	 */
	protected int modelMissCount = 0;

	/**
	 * Number of times an answer was NOT found in the store and a core was found.
	 */
	protected int coreMissCount = 0;

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
	 * Milliseconds spent to process requests that eventually produce a core.
	 */
	protected long coreTimeConsumption = 0;

	/**
	 * Milliseconds spent to process requests that do not produce an answer.
	 */
	protected long noAnswerTimeConsumption = 0;

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

	/**
	 * Construct an instance of a MODEL-CORE service.
	 *
	 * @param solver associated Green solver
	 */
	public ModelCoreService(Green solver) {
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
		reporter.report("  modelCount", modelCount);
		reporter.report("  coreCount", coreCount);
		reporter.report("  noAnswerCount", noAnswerCount);
		reporter.report("cacheHitCount", cacheHitCount);
		reporter.report("  modelHitCount", modelHitCount);
		reporter.report("  coreHitCount", coreHitCount);
		reporter.report("cacheMissCount", cacheMissCount);
		reporter.report("  modelMissCount", modelMissCount);
		reporter.report("  coreMissCount", coreMissCount);
		reporter.report("serviceTimeConsumption", serviceTimeConsumption);
		reporter.report("  modelTimeConsumption", modelTimeConsumption);
		reporter.report("  coreTimeConsumption", coreTimeConsumption);
		reporter.report("  noAnswerTimeConsumption", noAnswerTimeConsumption);
		reporter.report("solveTimeConsumption", solveTimeConsumption);
		reporter.report("innerTimeConsumption", innerTimeConsumption);
		reporter.report("keyTimeConsumption", keyTimeConsumption);
		super.report(reporter);
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
		invocationCount++;
		Object result = instance.getData(getClass());
		if (result == null) {
			result = solve0(instance);
			if (result != null) {
				instance.setData(getClass(), result);
			}
		}
		if (result instanceof ModelCore) {
			if (((ModelCore) result).isSat()) {
				modelCount++;
				modelTimeConsumption += System.currentTimeMillis() - startTime;
			} else {
				coreCount++;
				coreTimeConsumption += System.currentTimeMillis() - startTime;
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
	 * @param instance Green instance to solve
	 * @return the result of the computation as a {@link Model}
	 */
	protected ModelCore solve0(Instance instance) {
		long startTime = System.currentTimeMillis();
		String key = SERVICE_KEY + instance.getFullExpression().toString();
		keyTimeConsumption += System.currentTimeMillis() - startTime;
		ModelCore result = (ModelCore) store.get(key);
		if (result == null) {
			cacheMissCount++;
			result = solve1(instance);
			if (result != null) {
				if (result.isSat()) {
					modelMissCount++;
				} else {
					coreMissCount++;
				}
				store.put(key, result);
			}
		} else {
			cacheHitCount++;
			if (result.isSat()) {
				modelHitCount++;
			} else {
				coreHitCount++;
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
	 * @param instance Green instance to solve
	 * @return result of the computation as a {@link ModelCore}
	 */
	protected ModelCore solve1(Instance instance) {
		long startTime = System.currentTimeMillis();
		ModelCore result = modelCore(instance);
		solveTimeConsumption += System.currentTimeMillis() - startTime;
		return result;
	}

	/**
	 * Do the actual work to solve a Green instance.
	 *
	 * @param instance Green instance to solve
	 * @return the result of the computation as a {@link ModelCore}
	 */
	protected abstract ModelCore modelCore(Instance instance);

	// ======================================================================
	//
	// ENCAPSULATION OF A MODEL / CORE
	//
	// ======================================================================

	/**
	 * Encapsulation of a model or core. It is expected that all implementing
	 * services use this object.
	 */
	public static class ModelCore implements Serializable {

		/**
		 * Generate serial ID for serialization.
		 */
		private static final long serialVersionUID = -3031120875971006136L;

		/**
		 * Does this result represent a satisfying solution?
		 */
		private final boolean isSat;

		/**
		 * The model, if the solution is satisfying.
		 */
		private final Map<Variable, Constant> model;

		/**
		 * The core, if the solution is not satisfying.
		 */
		private final Set<Expression> core;

		/**
		 * Create an instance of a model / core.
		 *
		 * @param isSat is this solution satisfying?
		 * @param model the model for this solution (or {@code null})
		 * @param core  the core for this solution (or {@code null})
		 */
		public ModelCore(final boolean isSat, final Map<Variable, Constant> model, final Set<Expression> core) {
			this.isSat = isSat;
			this.model = model;
			this.core = core;
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

		/**
		 * Return the core that shows that there is no model.
		 *
		 * @return the unsatisfying code or {@code null}
		 */
		public Set<Expression> getCore() {
			return core;
		}

	}

}
