package za.ac.sun.cs.green.service.grulia;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.Stack;
import java.util.TreeSet;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.service.ModelCoreService;
import za.ac.sun.cs.green.service.SATService;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Based on Utopia (an SMT caching framework), which is defined in the paper:
 * "Heuristically Matching Formula Solution Spaces To Efficiently Reuse
 * Solutions" published at the International Conference on Software Engineering
 * (ICSE'17) by Andrea Aquino, Giovanni Denaro and Mauro Pezze'.
 *
 * Julia (Java version of Utopia Linear Integer Arithmetic) re-implemented to
 * improve GREEN. Julia is implemented as a service in GREEN -- Grulia.
 *
 * @author JH Taljaard (USnr 18509193)
 * @author Willem Visser (2018, 2019) (supervisor)
 * @author Jaco Geldenhuys (2017) (supervisor)
 */
class GruliaService extends SATService {

	// ======================================================================
	//
	// CONSTANTS THAT DEFINE THE BEHAVIOUR OF GRULIA
	//
	// ======================================================================

	/**
	 * The number of closest entries to extract.
	 */
	private static final int K = 10;

	/**
	 * Whether to substitute zero for variables not present in model.
	 */
	private static final boolean DEFAULT_ZERO = false;

	/**
	 * Tree-based repo or not.
	 */
	private static final boolean BINARY_TREE_REPO = true;

	/**
	 * The reference solutions.
	 * 
	 * For experiments, use -10000, 0, 100.
	 */
	private static final Integer[] REFERENCE_SOLUTION = { -10000, 0, 100 };

	/**
	 * Stores data of satisfiable formulas.
	 */
	private final Repository<ModelEntry> satRepo = BINARY_TREE_REPO ? new BinaryRepository<>()
			: new LinearRepository<>();

	/**
	 * Stores data of unsatisfiable formulas.
	 */
	private final Repository<CoreEntry> unsatRepo = BINARY_TREE_REPO ? new BinaryRepository<>()
			: new LinearRepository<>();

	// ======================================================================
	//
	// COUNTERS
	//
	// ======================================================================

	/**
	 * Number of times Grulia could not compute a result and that the instance is
	 * passed down to a solver.
	 */
	private long passedToSolverCount = 0;

	/**
	 * Number of times SatDelta is zero, which means that one of the reference
	 * solutions satisfied the expression to solve.
	 */
	private long zeroSatDeltaCount = 0;

	/**
	 * Number of times a model in the SAT repo was found to satisfy an expression.
	 */
	private int repoModelHitCount = 0;

	/**
	 * Number of times {@link #findSharedModel(Expression, SortedSet)} found no
	 * model in the SAT repo to satisfy an expression.
	 */
	private int satRepoMissCount = 0;

	/**
	 * Number of times some model did not satisfy some expression.
	 */
	private int repoModelFailCount = 0;

	/**
	 * Number of times a core in the UNSAT repo was found to subsume an expression.
	 */
	private int repoCoreHitCount = 0;

	/**
	 * Number of times {@link #findSharedCore(Expression)} found no core
	 * in the UNSAT repo to subsume an expression.
	 */
	private int unsatRepoMissCount = 0;

	/**
	 * Number of times some core did not subsume some expression.
	 */
	private int repoCoreFailCount = 0;

	/**
	 * Number of times the instance was relegated to an SMT solver.
	 */
	private int solverCount = 0;

	/**
	 * Number of times a new model was added to the satRepo.
	 */
	private int satRepoAddCount = 0;

	/**
	 * Number of times a new core was added to the unsatRepo.
	 */
	private int unsatRepoAddCount = 0;

	// ======================================================================
	//
	// TIME CONSUMPTION
	//
	// ======================================================================

	/**
	 * Milliseconds used to load the repos from the store.
	 */
	private long repoLoadTimeConsumption = 0;

	/**
	 * Milliseconds used to compute the set of variables in full expressions.
	 */
	private long variableSetTimeConsumption = 0;

	/**
	 * Milliseconds used to compute the SatDelta values.
	 */
	private long satDeltaTimeConsumption = 0;

	/**
	 * Milliseconds used to consult the SAT repo for models that might satisfy the
	 * expression.
	 */
	private long satRepoTimeConsumption = 0;

	/**
	 * Milliseconds used to consult the UNSAT repo for core that might be contained
	 * in the expression.
	 */
	private long unsatRepoTimeConsumption = 0;

	/**
	 * Milliseconds used to extract {@link #K} models from the SAT repo.
	 */
	private long modelExtractionTimeConsumption = 0;

	/**
	 * Milliseconds used to check if models satisfy expressions.
	 */
	private long modelEvaluationTimeConsumption = 0;

	/**
	 * Milliseconds spent evaluating potentially shared models (excluding model
	 * extraction time).
	 */
	private long sharedModelTimeConsumption = 0;

	/**
	 * Milliseconds used to extract {@link #K} cores from the UNSAT repo.
	 */
	private long coreExtractionTimeConsumption = 0;

	/**
	 * Milliseconds used to check if cores subsume expressions.
	 */
	private long coreEvaluationTimeConsumption = 0;

	/**
	 * Milliseconds spent evaluating potentially shared cores (excluding core
	 * extraction time).
	 */
	private long sharedCoreTimeConsumption = 0;

	// ======================================================================
	//
	// CONSTRUCTOR & METHODS
	//
	// ======================================================================

	/**
	 * Constructor for the Grulia service.
	 * 
	 * GruliaService recommends to run with Factorizer and Renamer.
	 *
	 * @param solver the {@link Green} solver this service will be added to
	 */
	public GruliaService(Green solver) {
		super(solver);
		long start = System.currentTimeMillis();
		for (String key : solver.getStore().keySet()) {
			Object entry = solver.getStore().get(key);
			if (entry instanceof ModelEntry) {
				satRepo.add((ModelEntry) entry);
			} else if (entry instanceof CoreEntry) {
				unsatRepo.add((CoreEntry) entry);
			}
		}
		repoLoadTimeConsumption += (System.currentTimeMillis() - start);
	}

	/**
	 * Overrides the method of the {@link SATService} superclass. This version makes
	 * provision for the fact that Grulia may or may not compute an answer to the
	 * process.
	 * 
	 * <ul>
	 * <li>In the former case, the result is stored "inside" the instance, and is
	 * picked up by {@link #allChildrenDone(Instance, Object)}. This method returns
	 * {@code null} to tell Green that the instance should not be passed down the
	 * tree.</li>
	 * <li>In the latter case, this routine returns the instance (as a singleton
	 * set).</li>
	 * </ul>
	 * 
	 * @param instance Green instance to solve
	 * @return {@code null} if Grulia finds an answer for the request or a singleton
	 *         set with the same instance
	 * @see za.ac.sun.cs.green.service.SATService#processRequest(za.ac.sun.cs.green.Instance)
	 */
	@SuppressWarnings("unchecked")
	@Override
	public Set<Instance> processRequest(Instance instance) {
		log.trace("processing {}", instance);
		long startTime = System.currentTimeMillis();
		Set<Instance> returnValue = null;
		Object result = instance.getData(getClass());
		if (result == null) {
			log.trace("not found inside instance");
			result = solve0(instance);
		}
		if (result == null) {
			log.trace("need to delegate to the solver");
			returnValue = Collections.singleton(instance);
			instance.setData(getClass(), returnValue);
			passedToSolverCount++;
		} else if (result instanceof Boolean) {
			log.trace("solved!");
			instance.setData(getClass(), result);
			if ((Boolean) result) {
				satCount++;
				satTimeConsumption += (System.currentTimeMillis() - startTime);
			} else {
				unsatCount++;
				unsatTimeConsumption += (System.currentTimeMillis() - startTime);
			}
		} else {
			assert (result instanceof Set<?>);
			returnValue = (Set<Instance>) result;
		}
		if (returnValue instanceof Set<?>) {
			log.trace("delegating to solver");
			instance.setData("SOLVER" + getClass(), Boolean.TRUE);
		}
		serviceTimeConsumption += (System.currentTimeMillis() - startTime);
		log.trace("returning {}", returnValue);
		return returnValue;
	}

	/**
	 * Overrides the method of the {@link SATService} superclass. This version does
	 * not consult the store.
	 *
	 * @param instance The instance to solve.
	 * @return satisfiability of the constraint.
	 * @see za.ac.sun.cs.green.service.SATService#solve0(za.ac.sun.cs.green.Instance)
	 */
	@Override
	protected Boolean solve0(Instance instance) {
		long startTime = System.currentTimeMillis();
		invocationCount++;
		Boolean result = solve(instance);
		solveTimeConsumption += (System.currentTimeMillis() - startTime);
		return result;
	}

	/**
	 * Executes the Utopia algorithm as described in the paper of Aquino.
	 *
	 * @param instance The instance to solve
	 * @return satisfiability of the constraint
	 */
	@Override
	protected Boolean solve(Instance instance) {
		long startTime = System.currentTimeMillis();
		Boolean result = null;
		Expression fullExpr = instance.getFullExpression();
		log.trace("fullExpr: {}", fullExpr);

		// Compute the set of variables.
		long startTime0 = System.currentTimeMillis();
		ExpressionVisitor expressionVisitor = new ExpressionVisitor();
		try {
			fullExpr.accept(expressionVisitor);
		} catch (VisitorException x) {
			log.fatal("encountered an exception -- this should not be happening!", x);
		}
		SortedSet<IntVariable> setOfVariables = expressionVisitor.getVariableSet();
		variableSetTimeConsumption += (System.currentTimeMillis() - startTime0);
		log.trace("set of variables: {}", () -> setOfVariables);

		// Compute SatDelta
		double satDelta = calculateSatDelta(fullExpr);
		log.trace("satDelta (average): {}", satDelta);
		if (satDelta == 0.0) {
			// The sat-delta computation produced a hit
			zeroSatDeltaCount++;
			result = true;
		}

		// Try to find a model in the SAT repo that satisfies the expression.
		if (result == null) {
			startTime0 = System.currentTimeMillis();
			result = findSharedModel(fullExpr, setOfVariables);
			satRepoTimeConsumption += (System.currentTimeMillis() - startTime0);
		}

		// Try to find a core in the UNSAT repo that subsumes the expression.
		if (result == null) {
			startTime0 = System.currentTimeMillis();
			result = findSharedCore(fullExpr);
			unsatRepoTimeConsumption += (System.currentTimeMillis() - startTime0);
		}

		// If result is still null, we have to pass the instance on to whatever
		// solver sits "below" this service. We don't have to "do" anything
		// about that here: returning null is sufficient.

		innerTimeConsumption += (System.currentTimeMillis() - startTime);
		return result;
	}

	/**
	 * Calculates the average SatDelta value of a given Expression.
	 *
	 * @param expr the given expression
	 * @return the average SatDelta value
	 */
	private double calculateSatDelta(Expression expr) {
		long startTime = System.currentTimeMillis();
		double result = 0.0;
		GruliaVisitor gruliaVisitor = new GruliaVisitor();
		try {
			for (int i = REFERENCE_SOLUTION.length - 1; i >= 0; i--) {
				gruliaVisitor.setReferenceValue(REFERENCE_SOLUTION[i]);
				expr.accept(gruliaVisitor);
				result += gruliaVisitor.getResult();
				log.trace("referenceSolution: {} satDelta: {}", REFERENCE_SOLUTION[i], gruliaVisitor.getResult());
			}
			result = result / REFERENCE_SOLUTION.length;
			expr.satDelta = result;
		} catch (VisitorException x) {
			log.fatal("encountered an exception -- this should not be happening!", x);
		}
		satDeltaTimeConsumption += (System.currentTimeMillis() - startTime);
		return result;
	}

	/**
	 * Find a reusable model (based on the satDelta distance) for the given
	 * expression. This method follows the following strategy:
	 * 
	 * <ol>
	 * <li>Find closest models in satRepo.</li>
	 * <li>For each such model, check if it satisfies the expression.</li>
	 * <li>If so, return {@code true}.</li>
	 * <li>If none of the models satisfies the expression, return {@code null}.</li>
	 * </ol>
	 *
	 * @param expr      expression to satisfy
	 * @param setOfVars variables in expression, passed to repo
	 * @return {@code true} if a satisfying model was found, otherwise {@code null}
	 */
	private Boolean findSharedModel(Expression expr, SortedSet<IntVariable> setOfVars) {
		log.trace("looking for shared models");
		satRepoMissCount++; // Assume that we won't find a model.
		ModelEntry anchorModel = new ModelEntry(expr.satDelta, null, setOfVars.size());
		Boolean result = null;
		if (satRepo.size() != 0) {
			long startTime = System.currentTimeMillis();
			List<ModelEntry> models = satRepo.getEntries(K, anchorModel);
			modelExtractionTimeConsumption += (System.currentTimeMillis() - startTime);
			log.trace("found {} close models", models.size());
			startTime = System.currentTimeMillis();
			for (ModelEntry model : models) {
				if (model == null) {
					break;
				}
				log.trace("investigating model {}", model);
				long startTime0 = System.currentTimeMillis();
				GruliaExpressionEvaluator satCheck = new GruliaExpressionEvaluator(model.getModel());
				try {
					expr.accept(satCheck);
				} catch (VisitorException x) {
					log.fatal("encountered an exception -- this should not be happening!", x);
				}
				modelEvaluationTimeConsumption += (System.currentTimeMillis() - startTime0);
				if (satCheck.isSat()) {
					log.trace("found satisfying model");
					result = true;
					repoModelHitCount++;
					satRepoMissCount--; // Initial assumption was false.
					break;
				} else {
					repoModelFailCount++;
				}
			}
			sharedModelTimeConsumption += (System.currentTimeMillis() - startTime);
		}
		log.trace("result: {}", result);
		return result;
	}

	/**
	 * Find a reusable core (based on the satDelta distance) for the given
	 * expression. This method follows the following strategy:
	 * 
	 * <ol>
	 * <li>Find closest cores in unsatRepo.</li>
	 * <li>For each such core, check if it subsumes the expression.</li>
	 * <li>If so, return {@code false}.</li>
	 * <li>If none of the mores subsumes the expression, return {@code null}.</li>
	 * </ol>
	 *
	 * @param expr      expression to subsume
	 * @return {@code false} if a subsuming core was found, otherwise {@code null}
	 */
	private Boolean findSharedCore(Expression expr) {
		log.trace("looking for shared cores");
		unsatRepoMissCount++; // Assume that we won't find a model.
		CoreEntry anchorCore = new CoreEntry(expr.satDelta, null);
		Boolean result = null;
		if (unsatRepo.size() != 0) {
			long startTime = System.currentTimeMillis();
			List<CoreEntry> cores = unsatRepo.getEntries(K, anchorCore);
			coreExtractionTimeConsumption += (System.currentTimeMillis() - startTime);
			log.trace("found {} close models", cores.size());
			startTime = System.currentTimeMillis();
			String exprStr = expr.toString();
			for (Entry core : cores) {
				if (core == null) {
					break;
				}
				long startTime0 = System.currentTimeMillis();
				Set<Expression> unsatCore = ((CoreEntry) core).getCore();
				boolean shared = (unsatCore.size() > 0);
				for (Expression clause : unsatCore) {
					if (!exprStr.contains(clause.toString())) {
						shared = false;
						break;
					}
				}
				coreEvaluationTimeConsumption += (System.currentTimeMillis() - startTime0);
				if (shared) {
					log.trace("found subsuming core");
					result = false;
					repoCoreHitCount++;
					unsatRepoMissCount--; // Initial assumption was false.
					break;
				} else {
					repoCoreFailCount++;
				}
			}
			sharedCoreTimeConsumption += (System.currentTimeMillis() - startTime);
		}
		log.trace("result: {}", result);
		return result;
	}

	@Override
	public Object allChildrenDone(Instance instance, Object result) {
		if (instance.getData("SOLVER" + getClass()) != null) {
			solverCount++;
			Boolean isSat = ModelCoreService.isSat(instance);
			double satDelta = instance.getFullExpression().satDelta;
			log.trace("solver was invoked, isSat: {} satDelta: {}", isSat, satDelta);
			if (isSat) {
				Map<Variable, Constant> model = ModelCoreService.getModel(instance);
				ModelEntry newEntry = new ModelEntry(satDelta, model);
				log.trace("adding {} to satRepo", model);
				satRepo.add(newEntry);
				satRepoAddCount++;
				satCount++;
			} else {
				Set<Expression> core = ModelCoreService.getCore(instance);
				CoreEntry newEntry = new CoreEntry(satDelta, core);
				log.trace("adding {} to unsatRepo", core);
				unsatRepo.add(newEntry);
				unsatRepoAddCount++;
				unsatCount++;
			}
			return isSat;
		} else {
			return instance.getData(getClass());
		}
	}

	@Override
	public void report(Reporter reporter) {
		super.report(reporter);
		reporter.setContext(getClass().getSimpleName());

		// Counters
		reporter.report("passedToSolverCount", passedToSolverCount);
		reporter.report("zeroSatDeltaCount", zeroSatDeltaCount);
		reporter.report("repoModelHitCount", repoModelHitCount);
		reporter.report("satRepoMissCount", satRepoMissCount);
		reporter.report("repoModelFailCount", repoModelFailCount);
		reporter.report("repoCoreHitCount", repoCoreHitCount);
		reporter.report("unsatRepoMissCount", unsatRepoMissCount);
		reporter.report("repoCoreFailCount", repoCoreFailCount);
		reporter.report("solverCount", solverCount);
		reporter.report("satRepoAddCount", satRepoAddCount);
		reporter.report("unsatRepoAddCount", unsatRepoAddCount);

		// Time consumption
		reporter.report("repoLoadTimeConsumption", repoLoadTimeConsumption);
		reporter.report("variableSetTimeConsumption", variableSetTimeConsumption);
		reporter.report("satDeltaTimeConsumption", satDeltaTimeConsumption);
		reporter.report("satRepoTimeConsumption", satRepoTimeConsumption);
		reporter.report("unsatRepoTimeConsumption", unsatRepoTimeConsumption);
		reporter.report("modelExtractionTimeConsumption", modelExtractionTimeConsumption);
		reporter.report("modelEvaluationTimeConsumption", modelEvaluationTimeConsumption);
		reporter.report("sharedModelTimeConsumption", sharedModelTimeConsumption);
		reporter.report("coreExtractionTimeConsumption", coreExtractionTimeConsumption);
		reporter.report("coreEvaluationTimeConsumption", coreEvaluationTimeConsumption);
		reporter.report("sharedCoreTimeConsumption", sharedCoreTimeConsumption);
	}

	// ======================================================================
	//
	// VISITOR TO COLLECT VARIABLES
	//
	// ======================================================================

	private static class ExpressionVisitor extends Visitor {

		private final SortedSet<IntVariable> variableSet;

		private boolean linearInteger;

		ExpressionVisitor() {
			variableSet = new TreeSet<>();
			linearInteger = true;
		}

		SortedSet<IntVariable> getVariableSet() {
			return variableSet;
		}

		@Override
		public void postVisit(Variable variable) {
			if (linearInteger) {
				if (variable instanceof IntVariable) {
					variableSet.add((IntVariable) variable);
				} else {
					linearInteger = false;
				}
			}
		}
	}

	// ======================================================================
	//
	// VISITOR TO CALCULATE SATDELTA
	//
	// ======================================================================

	/**
	 * Visitor to compute the SatDelta value for an expressions given a reference
	 * value.
	 */
	private static class GruliaVisitor extends Visitor {

		/**
		 * Local stack to calculate the SatDelta value
		 */
		private final Stack<Integer> stack = new Stack<>();

		/**
		 * Value used for all variables.
		 */
		private Integer referenceValue = null;

		/**
		 * Result of computation. We "cache" it so that we can call {@link #getResult()}
		 * more than once.
		 */
		private Double result = null;

		/**
		 * Clear the stack and set the reference value in preparation for a run of the
		 * visitor.
		 * 
		 * @param referenceValue the new reference value
		 */
		void setReferenceValue(int referenceValue) {
			stack.clear();
			result = null;
			this.referenceValue = referenceValue;
		}

		/**
		 * Return the SatDelta value of the expression for the reference solution
		 * specified by {@link #referenceValue}.
		 * 
		 * @return the SatDelta value
		 */
		double getResult() {
			if (result == null) {
				result = 0.0 + stack.pop();
			}
			return result;
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see
		 * za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.Variable)
		 */
		@Override
		public void postVisit(Variable variable) {
			stack.push(referenceValue);
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.
		 * IntConstant)
		 */
		@Override
		public void postVisit(IntConstant constant) {
			stack.push(constant.getValue());
		}

		/**
		 * Calculates the SatDelta value for a given operation and pushes the result
		 * onto the stack.
		 *
		 * The distance of an expression from a set of reference models is called
		 * "SatDelta" and is defined in the paper: "Heuristically Matching Formula
		 * Solution Spaces To Efficiently Reuse Solutions" published at the
		 * International Conference on Software Engineering (ICSE'17) by Andrea Aquino,
		 * Giovanni Denaro and Mauro Pezze'.
		 *
		 * @param operation the current operation working with
		 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.Operation)
		 */
		@Override
		public void postVisit(Operation operation) {
			Integer left = null, right = null;
			assert (operation.getOperator().getArity() == 2);
			if (!stack.isEmpty()) {
				right = stack.pop();
			}
			if (!stack.isEmpty()) {
				left = stack.pop();
			}
			assert (left != null) && (right != null);
			switch (operation.getOperator()) {
			case LT:
				stack.push(left >= right ? left - right + 1 : 0);
				break;
			case LE:
				stack.push(left > right ? left - right : 0);
				break;
			case ADD:
			case OR:
			case AND:
				stack.push(left + right);
				break;
			case GT:
				stack.push(left <= right ? right - left + 1 : 0);
				break;
			case GE:
				stack.push(left < right ? right - left : 0);
				break;
			case EQ:
				stack.push(!left.equals(right) ? Math.abs(left - right) : 0);
				break;
			case NE:
				stack.push(left.equals(right) ? 1 : 0);
				break;
			case MUL:
				stack.push(left * right);
				break;
			case SUB:
				stack.push(Math.abs(Math.abs(right) - Math.abs(left)));
				break;
			case MOD:
				stack.push(Math.floorMod(left, right));
				break;
			default:
				stack.push(0);
				break;
			}
		}

	}

	// ======================================================================
	//
	// VISITOR TO CHECK IF VARIABLE ASSIGNMENT SATISFIES AN EPXRESSION
	//
	// ======================================================================

	/**
	 * Visitor to compute expression values for a given variable assignment.
	 */
	private static class GruliaExpressionEvaluator extends Visitor {

		/**
		 * Local stack for the evaluation of the expression.
		 */
		private final Stack<Object> evalStack = new Stack<>();

		/**
		 * Mapping from variables to values.
		 */
		private final Map<Variable, Constant> modelMap;

		GruliaExpressionEvaluator(Map<Variable, Constant> modelMap) {
			super();
			this.modelMap = modelMap;
		}

		/**
		 * Return the satisfiability status of the expression.
		 *
		 * @return {@code true} if the expression is satisfied, otherwise {@code false}
		 */
		Boolean isSat() {
			if (evalStack.isEmpty()) {
				return false;
			}
			Object top = evalStack.pop();
			return (top instanceof Boolean) && (Boolean) top;
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see
		 * za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.Variable)
		 */
		@Override
		public void postVisit(Variable variable) {
			Constant value = modelMap.get(variable);
			if (value instanceof IntConstant) {
				evalStack.push(((IntConstant) value).getValue());
			} else {
				evalStack.push(0);
			}
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.
		 * IntConstant)
		 */
		@Override
		public void postVisit(IntConstant constant) {
			evalStack.push(constant.getValue());
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see
		 * za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.Operation)
		 */
		@Override
		public void postVisit(Operation operation) {
			Object left = null, right = null;
			int arity = operation.getOperator().getArity();
			if (arity == 2) {
				if (!evalStack.isEmpty()) {
					right = evalStack.pop();
				}
				if (!evalStack.isEmpty()) {
					left = evalStack.pop();
				}
				assert (left != null) && (right != null);
			} else if (arity == 1) {
				if (!evalStack.isEmpty()) {
					left = evalStack.pop();
				}
				assert (left != null);
			}
			switch (operation.getOperator()) {
			case LE:
				evalStack.push(((Integer) left) <= ((Integer) right));
				break;
			case LT:
				evalStack.push((Integer) left < (Integer) right);
				break;
			case AND:
				evalStack.push((Boolean) left && (Boolean) right);
				break;
			case ADD:
				evalStack.push((Integer) left + (Integer) right);
				break;
			case SUB:
				evalStack.push((Integer) left - (Integer) right);
				break;
			case EQ:
				evalStack.push(left.equals(right));
				break;
			case GE:
				evalStack.push((Integer) left >= (Integer) right);
				break;
			case GT:
				evalStack.push((Integer) left > (Integer) right);
				break;
			case MUL:
				evalStack.push((Integer) left * (Integer) right);
				break;
			case OR:
				evalStack.push((Boolean) left || (Boolean) right);
				break;
			case NE:
				evalStack.push(!left.equals(right));
				break;
			case MOD:
				evalStack.push((Integer) left % (Integer) right);
				break;
			default:
				break;
			}
		}

	}

}
