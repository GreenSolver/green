package za.ac.sun.cs.green.service.grulia;

import za.ac.sun.cs.green.expr.*;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.service.ModelCoreService;
import za.ac.sun.cs.green.service.SATService;
import za.ac.sun.cs.green.util.Configuration;
import za.ac.sun.cs.green.util.Reporter;

import java.util.*;

/**
 * @date: 2017/06/02
 * @author: JH Taljaard.
 * Student Number: 18509193.
 * Supervisor:  Willem Visser   (2018),
 *              Jaco Geldenhuys (2017)
 *
 * Description:
 * Utopia (an SMT caching framework) is defined in the paper:
 * "Heuristically Matching Formula Solution Spaces To Efficiently Reuse Solutions"
 * published at the International Conference on Software Engineering (ICSE'17)
 * by Andrea Aquino, Giovanni Denaro and Mauro Pezze'.
 *
 * Julia (Java version of Utopia Linear Integer Arithmetic)
 * re-implemented to improve GREEN. Julia is implemented
 * as a service in GREEN -- Grulia.
 *
 */
public class GruliaService extends SATService {

	/*
	##################################################################
	####################### Variables to set #########################
	##################################################################
	*/

	/**
	 * The number of closest entries to extract
	 */
	private final int Ks = 10;

	/**
	 * Substitute zero if is variable not present in model
	 */
	private final boolean default_zero = false;

	/**
	 * TreeSet repo or not.
	 */
	private final boolean binarysearch = true;

    /**
     * Use Z3 with java bindings or commandline.
     */
//	private boolean z3java = false;

	/**
	 * The value of the reference solution.
	 * For experiments: -10000, 0, 100
	 */
	private static final Integer[] REFERENCE_SOLUTION = {-10000, 0, 100};
	private static final int REF_SOL_SIZE = REFERENCE_SOLUTION.length;

	/**
	 * For debugging purposes.
	 */
	public static final boolean DEBUG = false;

	/*##################################################################*/

	/**
	 * Stores data of satisfiable formulas.
	 */
	private Repo SAT_REPO;
    /**
     * Stores data of unsatisfiable formulas.
     */
	private Repo UNSAT_REPO;

	/**
	 * Instance of Green to do model checking.
	 */
	protected Green modelChecker;

	/**
	 * A counter to keep track of which REFERENCE_SOLUTION
	 * currently working with. This is for GruliaVisitor.
	 */
	protected static int COUNTER;

	/*
	 ##################################################################
	 #################### For logging purposes ########################
	 ##################################################################
	*/

	/**
	 * Number of times the service has been invoked.
	 */
	private int invocationCount = 0;

	/**
	 * Number of times some model satisfied some expression (in a run).
	 */
	private static int satModelCount = 0;

    /**
     * Number of times some unsat-core was in some expression (in a run).
     */
	private static int sharesUnsatCoresCount = 0;

	/**
	 * Total Number of times some model satisfied some expression (across runs).
	 */
	private int totSatModelCount = 0;

    /**
     * Total Number of times some unsat-core was in some expression (across runs).
     */
	private int totUnsatCoresCount = 0;

	/**
	 * Number of times some model did not satisfy some expression.
	 */
	private int unsatModelCount = 0;

	/**
	 * Number of times the SMT solver was called.
	 */
	private static int solverCount = 0;

	/**
	 * Number of models cached.
	 */
	private static int entryCount = 0;

	/**
	 * Number of satisfied expressions (for a run).
	 */
	private static int satCount = 0;

	/**
	 * Total number of satisfied expressions (across runs).
	 */
	private int totSatCount = 0;

    /**
     * Total number of unsatisfied expressions (across runs).
     */
	private int totUnsatCount = 0;

	/**
	 * Number of unsatisfied expressions.
	 */
	private static int unsatCount = 0;

	/**
	 * Execution Time of the service.
	 */
	private static long timeConsumption = 0;

	private static long satTimeConsumption = 0;

	private static long unsatTimeConsumption = 0;

	/**
	 * Number of times a valid entry found in the Repo.
	 */
	private static int satCacheHitCount = 0;

	private static int unsatCacheHitCount = 0;

	/**
	 * Number of times a valid entry was not found in the satRepo.
	 */
	private static int satCacheMissCount = 0;

	private static int unsatCacheMissCount = 0;

	/**
	 * Total number of variables encountered.
	 */
//	private int totalVariableCount = 0;

	/**
	 * To keep track of the already seen variables.
	 */
//	protected static ArrayList<IntVariable> newVariables;

//	protected static ArrayList<Double> satDeltaValues;

//	protected static ArrayList<Double> satDeltaValuesInRepo;

	protected static int[] modelNumbers;

	/**
	 * Total number of new variables encountered.
	 */
	protected static int newVariableCount = 0;

	/*** Resetting counters ***/
	private static void setSatModelCount(int x) {
		satModelCount = x;
	}

	private static void setUnsatCoreCount(int x) {
		sharesUnsatCoresCount = x;
	}

	private static void setSolverCount(int x) {
		solverCount = x;
	}

	private static void setEntryCount(int x) {
		entryCount = x;
	}

	private static void setSatCount(int x) {
		satCount = x;
	}

	private static void setUnsatCount(int x) {
		unsatCount = x;
	}

	private static void setTimeConsumption(long x) {
		timeConsumption = x;
		satTimeConsumption = x;
		unsatTimeConsumption = x;
	}

	private static void setCacheHitCount(int x) { satCacheHitCount = x; }
	private static void setUnsatCacheHitCount(int x) { unsatCacheHitCount = x; }
	private static void setCacheMissCount(int x) { satCacheMissCount = x; }
	private static void setUnsatCacheMissCount(int x) { unsatCacheMissCount = x; }

	public static void reset() {
		setCacheHitCount(0);
		setCacheMissCount(0);
		setEntryCount(0);
		setSatCount(0);
		setSatModelCount(0);
		setSolverCount(0);
		setTimeConsumption(0L);
		setUnsatCount(0);
		setUnsatCacheHitCount(0);
		setUnsatCacheMissCount(0);
		setUnsatCoreCount(0);
	}

	/*##################################################################*/

	/**
	 * Constructor for the basic service. It simply initializes its three
	 * attributes.
	 *
	 * GuliaService recommends to run with Factorizer and Renamer.
	 *
	 * @param solver the {@link Green} solver this service will be added to
	 */
	public GruliaService(Green solver) {
		super(solver);

		if (binarysearch) {
			SAT_REPO = new SatRepoB(default_zero);
			UNSAT_REPO = new UnsatRepoB(default_zero);
		} else {
			SAT_REPO = new SatRepoA(default_zero);
			UNSAT_REPO = new UnsatRepoA(default_zero);
		}

//		newVariables = new ArrayList<IntVariable>();
//		satDeltaValues = new ArrayList<Double>();
//		satDeltaValuesInRepo = new ArrayList<Double>();
		modelNumbers = new int[Ks];

		// Initializes and configure Green instance for model checking.
		modelChecker = new Green();
		Properties props = new Properties();
		props.setProperty("green.services", "solver");

		props.setProperty("green.service.solver", "(bounder (z3mc))");
        props.setProperty("green.service.solver.bounder", "za.ac.sun.cs.green.service.bounder.BounderService");
        props.setProperty("green.service.solver.z3mc", "za.ac.sun.cs.green.service.z3.ModelCoreZ3Service");

//        props.setProperty("green.service.solver", "(bounder (z3m))");
//        props.setProperty("green.service.solver.bounder", "za.ac.sun.cs.green.service.bounder.BounderService");
//		props.setProperty("green.service.solver.z3m", "za.ac.sun.cs.green.service.z3.ModelZ3JavaService");

		Configuration config = new Configuration(modelChecker, props);
		config.configure();
	}

	protected static Integer getReferenceSolution(int a) {
		return REFERENCE_SOLUTION[a];
	}

	@Override
	protected Boolean solve(Instance instance) {
		long startTime = System.currentTimeMillis();
		Boolean SAT;
		SAT = solve0(instance);
		long a = System.currentTimeMillis() - startTime;
		timeConsumption += a;
		if (SAT) {
			satTimeConsumption += a;
		} else {
			unsatTimeConsumption += a;
		}
		return SAT;
	}

	private long time_of_sat_cache = 0;
	private long time_of_unsat_cache = 0;
	private long time_of_solver = 0;
	private long time_of_satdelta_calculation = 0;
	private long count_of_0_sd = 0;

	private Boolean solve0(Instance instance) {
		Double satDelta;
		long startTime;
		boolean STATUS = false;

		invocationCount++;
		Expression target = instance.getFullExpression();
		ExprVisitor exprVisitor = new ExprVisitor();

		try {
			target.accept(exprVisitor);
		} catch (VisitorException x) {
			log.fatal("encountered an exception -- this should not be happening!", x);
		}

        SortedSet<IntVariable> setOfVars = exprVisitor.getVariableSet();

		startTime = System.currentTimeMillis();
		satDelta = calculateSATDelta(target);
		time_of_satdelta_calculation += System.currentTimeMillis()- startTime;
		if (satDelta == 0.0) {
			// The sat-delta computation produced a hit
			count_of_0_sd++;
			return true;
		}

		startTime = System.currentTimeMillis();
		STATUS = sharesModel(satDelta, target, setOfVars);
		time_of_sat_cache += System.currentTimeMillis() - startTime;
		if (STATUS) {
			// if model satisfied expression, i.e. query is sat
			// return immediately
			return true;
		}

		startTime = System.currentTimeMillis();
		STATUS = sharesUnsatCores(satDelta, target, setOfVars);
		time_of_unsat_cache += System.currentTimeMillis() - startTime;
		if (STATUS) {
			// if shares unsat cores i.e. query is unsat
			// return immediately
			return false;
		}

		// else continue and calculate solution
		// call solver & store
		startTime = System.currentTimeMillis();
//		if (!z3java) {
			STATUS = solver1(satDelta, target);
//		} else {
//			STATUS = solver2(satDelta, target);
//		}
		time_of_solver += System.currentTimeMillis() - startTime;
		return STATUS;
	}

	/**
	 * Calculates the average SATDelta value of a given Expression.
	 *
	 * @param expr the given Expression.
	 * @return the average SATDelta value.
	 */
	private Double calculateSATDelta(Expression expr) {
		Double result = 0.0;
		GruliaVisitor gVisitor = new GruliaVisitor();
		gVisitor.setRefSol(REFERENCE_SOLUTION);

		try {
			for (int i = 0; i < REF_SOL_SIZE; i++) {
			    gVisitor.setRefIndex(i);
				expr.accept(gVisitor);
				Double x = gVisitor.getResult();
				result += x;
			}

			// calculate average SAT-Delta
			result = result/REF_SOL_SIZE;
//			satDeltaValues.add(result);
//			totalVariableCount += VARS.size();

		} catch (VisitorException x) {
			log.fatal("encountered an exception -- this should not be happening!", x);
		}

		return result;
	}

	/**
	 * Finds reusable models for the given Expression from the given SATDelta
	 * value.
	 *
	 * @param satDelta the SATDelta value for the model filtering
	 * @param expr the Expression to solve
	 * @return SAT - if the Expression could be satisfied from previous models
	 */
	private long time_of_models_extraction = 0;
	private long time_of_models_testing = 0;
	private long time_of_model_eval = 0;
//	private long count_of_models_extraction = 0;

	private Boolean sharesModel(Double satDelta, Expression expr, SortedSet<IntVariable> setOfVars) {
		/*
		 * Check if SAT-Delta is in table
		 * If in table -> test if model satisfies
		 * If not take next (k) closest SAT-Delta
		 * If not satisfied, call solver
		 */
		if (SAT_REPO.size() != 0) {
			long start = System.currentTimeMillis();
            long start1;
//			count_of_models_extraction++;
			Entry[] temp = SAT_REPO.extract(satDelta, setOfVars, Ks);
			time_of_models_extraction += System.currentTimeMillis()-start;
			if (temp[0] == null) {
				satCacheMissCount++;
				return false;
			}

			int i = 0;
			start = System.currentTimeMillis();
			for (Entry entry : temp) {
				// extract model
				if (entry == null) {
					break;
				}

//				MODEL_MAPPING = ((SatEntry) entry).getSolution();
				// test model satisfiability
				start1 = System.currentTimeMillis();
				GruliaExpressionEvaluator exprSATCheck = new GruliaExpressionEvaluator();
				exprSATCheck.setModelMap(((SatEntry) entry).getSolution());
				try {
					expr.accept(exprSATCheck);
				} catch (VisitorException x) {
					log.fatal("encountered an exception -- this should not be happening!", x);
				}
                time_of_model_eval += System.currentTimeMillis()-start1;

				if (exprSATCheck.isSat()) {
					// already in repo,
					// don't have to do anything
					satModelCount++;
					satCount++;
					totSatCount++;
					totSatModelCount++;
					satCacheHitCount++;
					modelNumbers[i]++;
					time_of_models_testing += System.currentTimeMillis() - start;
					return true;
				} else {
					unsatModelCount++;
				}

				i++;
			}
			time_of_models_testing += System.currentTimeMillis() - start;
			// call solver
		} // else :: repo empty -> call solver

		satCacheMissCount++;
		return false;
	}

	private Boolean sharesUnsatCores(Double satDelta, Expression expr, SortedSet<IntVariable> setOfVars) {
		/*
		 * Check if SAT-Delta is in table
		 * If in table -> test if shares unsat cores
		 * If not take next (k) closest SAT-Delta
		 * If not sharing unsat core, call solver
		 */
		if (UNSAT_REPO.size() != 0) {

			Entry[] temp = UNSAT_REPO.extract(satDelta, setOfVars, Ks);
			boolean shares;

			if (temp[0] == null) {
				unsatCacheMissCount++;
				return false;
			}

			String exprStr = expr.toString();
			for (Entry entry : temp) {
				// extract expression
				if (entry == null) {
					break;
				}

				Set<Expression> core = ((UnsatEntry) entry).getSolution();
				shares = true;
				for (Expression clause : core) {
					if (!exprStr.contains(clause.toString())) {
						shares = false;
						break;
					}
				}
				if (shares) {
					sharesUnsatCoresCount++;
					unsatCount++;
					totUnsatCount++;
					totUnsatCoresCount++;
					unsatCacheHitCount++;
					return true;
				}
			}
			// call solver
		} // else :: repo empty -> call solver

		unsatCacheMissCount++;
		return false;
	}

	/**
	 * Calls the model checker to solve the Expression.
	 * If the Expression could be satisfied, its model and SATDelta value is stored.
	 *
	 * @param satDelta the SATDelta value to store as key.
	 * @param expr the Expression to store
	 * @return SAT - if the Expression could be satisfied.
	 */
	private Boolean solver1(Double satDelta, Expression expr) {
		// Get model for formula
		Boolean SAT;
		Instance i = new Instance(modelChecker, null, expr);
		solverCount++;

		Instance j = (Instance) i.request("solver");
		if (ModelCoreService.isSat(j)) {
			Map<Variable, Constant> solution = ModelCoreService.getModel(j);
			SatEntry newEntry = new SatEntry(satDelta, solution);

			SAT_REPO.add(newEntry);
//			satDeltaValuesInRepo.add(satDelta);
			entryCount++;
			totSatCount++;
			satCount++;
			SAT = true;
		} else {
			Set<Expression> core = ModelCoreService.getCore(j);
			UnsatEntry newEntry  = new UnsatEntry(satDelta, core);

			UNSAT_REPO.add(newEntry );
			unsatCount++;
			SAT = false;
		}
		return SAT;
	}

    private Boolean solver2(Double satDelta, Expression expr) {
        // Get model for formula
        Boolean SAT = false;
        Instance i = new Instance(modelChecker, null, expr);
        solverCount++;

        Object result_t = i.request("solver");

        if (result_t != null) {
            // is feasible
            @SuppressWarnings("unchecked")
            Map<Variable, Integer> solution = (Map<Variable, Integer>) result_t;
            SatEntry tempEntry = new SatEntry(satDelta, solution, false);

            SAT_REPO.add(tempEntry);
//            satDeltaValuesInRepo.add(satDelta);
            entryCount++;
            totSatCount++;
            satCount++;
            SAT = true;
        } else {
            UnsatEntry tempEntry = new UnsatEntry(satDelta, Collections.singleton(expr));

            UNSAT_REPO.add(tempEntry);
            unsatCount++;
            SAT = false;
        }
        return SAT;
    }

	/**
	 * Display the list of values as a histogram.
	 *
	 * @param reporter the output reporter
	 * @param list the list containing values of type Double
	 */
	private void displayAsHistogram(Reporter reporter, ArrayList<Double> list) {
		HashMap<Double, Integer> histogram = new HashMap<Double, Integer>();

		for (Double x : list) {
			histogram.merge(x, 1, (a, b) -> a + b);
		}

		reporter.report(getClass().getSimpleName(), histogram.toString());
	}

	/**
	 * Display histogram array of values
	 * @param reporter
	 * @param a
	 */
	private void displayAsHistogram(Reporter reporter, int[] a) {
		StringBuilder s = new StringBuilder();
		s.append("{");
		int n = Ks - 1;
		for (int i = 0; i < n; i++) {
		   s.append(i + 1).append("=").append(a[i]).append(", ");
		}
		s.append(Ks + "=").append(a[Ks - 1]).append("}");
		reporter.report(getClass().getSimpleName(), s.toString());
	}

	/**
	 * Calculates the distribution of the SATDelta values, for the reporter.
	 * @param reporter the reporter
	 * @param list SATDelta values
	 */
	private void distribution(Reporter reporter, ArrayList<Double> list) {
		Double avg = 0.0;
		Collections.sort(list);

		reporter.report(getClass().getSimpleName(),"minSATDelta = " + list.get(0));
		reporter.report(getClass().getSimpleName(),"maxSATDelta = " + list.get(list.size()-1));

		for (Double x : list) {
			avg += x;
		}

		avg = avg/list.size();

		reporter.report(getClass().getSimpleName(),"meanSATDelta = " + avg);

		Double sum = 0.0;

		for (Double x : list) {
			sum += Math.pow((x - avg), 2);
		}

		Double sigma = sum/(list.size()-1);
		sigma = Math.sqrt(sigma);

		reporter.report(getClass().getSimpleName(),"standard deviation of SATDelta = " + sigma);

		Double cv = sigma/avg;

		reporter.report(getClass().getSimpleName(),"coefficient of variation of SATDelta = " + cv);

	}

	@Override
	public void report(Reporter reporter) {
		modelChecker.report();
		reporter.report(getClass().getSimpleName(), "invocations = " + invocationCount);
//        reporter.report(getClass().getSimpleName(), "totalVariables = " + totalVariableCount);
//        reporter.report(getClass().getSimpleName(), "totalNewVariables = " + newVariableCount);
//        reporter.report(getClass().getSimpleName(), "totalOldVariables = " + (totalVariableCount-newVariableCount));
		reporter.report(getClass().getSimpleName(), "total SAT queries = " + totSatCount);
		reporter.report(getClass().getSimpleName(), "SAT queries = " + satCount);
		reporter.report(getClass().getSimpleName(), "UNSAT queries = " + unsatCount);
		reporter.report(getClass().getSimpleName(), "satCacheHitCount = " + satCacheHitCount);
		reporter.report(getClass().getSimpleName(), "satCacheMissCount = " + satCacheMissCount);
		reporter.report(getClass().getSimpleName(), "unsatCacheHitCount = " + unsatCacheHitCount);
		reporter.report(getClass().getSimpleName(), "unsatCacheMissCount = " + unsatCacheMissCount);
		reporter.report(getClass().getSimpleName(), "total Models reused = " + totSatModelCount);
		reporter.report(getClass().getSimpleName(), "Models reused = " + satModelCount);
		reporter.report(getClass().getSimpleName(), "Models tested unsat = " + unsatModelCount);
		reporter.report(getClass().getSimpleName(), "unsat cores reused = " + sharesUnsatCoresCount);
		reporter.report(getClass().getSimpleName(), "number of times SMT solver was called = " + solverCount);
		reporter.report(getClass().getSimpleName(), "SAT entries added to cache = " + entryCount);
/*
		if (false) {
			// Sat delta values
			reporter.report(getClass().getSimpleName(), "totalSatDeltaValues distribution: ");
			distribution(reporter, satDeltaValues);
			reporter.report(getClass().getSimpleName(), "SatDeltaValues in Repo distribution: ");
			distribution(reporter, satDeltaValuesInRepo);

			reporter.report(getClass().getSimpleName(), "Display SAT-Delta as histogram: ");
			displayAsHistogram(reporter, satDeltaValues);
			reporter.report(getClass().getSimpleName(), "Display SAT-Delta (in repo) as histogram: ");
			displayAsHistogram(reporter, satDeltaValuesInRepo);
		}

		if (false) {
			// Model numbers
			reporter.report(getClass().getSimpleName(), "Display ModelNumbers as histogram: ");
			displayAsHistogram(reporter, modelNumbers);
		}
*/
		reporter.report(getClass().getSimpleName(), "K Model Extract time = " + time_of_models_extraction);
//		reporter.report(getClass().getSimpleName(), "K Model Extract count = " + count_of_models_extraction);
		reporter.report(getClass().getSimpleName(), "K Model testing time = " + time_of_models_testing);
		reporter.report(getClass().getSimpleName(), "Model evaluation time = " + time_of_model_eval);
		reporter.report(getClass().getSimpleName(), "Count of 0 satdelta  = " + count_of_0_sd);
		reporter.report(getClass().getSimpleName(), "Sat Cache check time = " + time_of_sat_cache);
		reporter.report(getClass().getSimpleName(), "Unsat Cache check time = " + time_of_unsat_cache);
		reporter.report(getClass().getSimpleName(), "Solver-call time = " + time_of_solver);
		reporter.report(getClass().getSimpleName(), "Sat Delta computation time = " + time_of_satdelta_calculation);
		reporter.report(getClass().getSimpleName(), "timeConsumption = " + timeConsumption);
		reporter.report(getClass().getSimpleName(), "satTimeConsumption = " + satTimeConsumption);
		reporter.report(getClass().getSimpleName(), "unsatTimeConsumption = " + unsatTimeConsumption);

	}

	private static class ExprVisitor extends Visitor {

		private SortedSet<IntVariable> variableSet;

		private boolean unsatisfiable;

		private boolean linearInteger;

		public ExprVisitor() {
			variableSet = new TreeSet<IntVariable>();
			unsatisfiable = false;
			linearInteger = true;
		}

		public SortedSet<IntVariable> getVariableSet() {
			return variableSet;
		}

		@Override
		public void postVisit(Variable variable) {
			if (linearInteger && !unsatisfiable) {
				if (variable instanceof IntVariable) {
					variableSet.add((IntVariable) variable);
				} else {
					linearInteger = false;
				}
			}
		}
	}
}


class GruliaVisitor extends Visitor {

	/*
	 * Local stack to calculate the SAT-Delta value
	 */
	private Stack<Integer> stack = new Stack<Integer>();

	private Integer[] referenceSolution;
	private int index;

	public void setRefSol(Integer[] models) {
        referenceSolution = models;
    }

    public void setRefIndex(int index) {
	    this.index = index;
    }

	/**
	 * @return x - SAT-Delta value
	 */
	public Double getResult() {
		Double x = 0.0;
		x += stack.pop();
		return x;
	}

	@Override
	public void postVisit(Expression expression) throws VisitorException {
		super.postVisit(expression);
	}

	@Override
	public void postVisit(Variable variable) throws VisitorException {
		super.postVisit(variable);

//		if (!GruliaService.newVariables.contains((IntVariable) variable)) {
//			GruliaService.newVariables.add((IntVariable) variable);
//			GruliaService.newVariableCount++;
//		}

		Integer value = referenceSolution[index];
		stack.push(value);
	}

	@Override
	public void postVisit(IntConstant constant) throws VisitorException {
		super.postVisit(constant);
		stack.push(constant.getValue());
	}

	@Override
	public void postVisit(Operation operation) throws VisitorException {
		super.postVisit(operation);
		SATDelta(operation, stack);
	}

	/**
	 * Calculates the SAT-Delta value for a given operation and
	 * pushes the result to a given stack.
	 *
	 * The distance of an expression from a set of reference models is called
	 * "SatDelta" and is defined in the paper:
	 * "Heuristically Matching Formula Solution Spaces To Efficiently Reuse Solutions"
	 * published at the International Conference on Software Engineering (ICSE'17)
	 * by Andrea Aquino, Giovanni Denaro and Mauro Pezze'.
	 *
	 * @param operation the current operation working with
	 * @param stack the stack to push the result to
	 */
	private void SATDelta(Operation operation, Stack<Integer> stack) {
		Integer l = null;
		Integer r = null;

		int arity = operation.getOperator().getArity();
		if (arity == 2) {
			if (!stack.isEmpty()) {
				r = stack.pop();
			}
			if (!stack.isEmpty()) {
				l = stack.pop();
			}
		}

		Operation.Operator op = operation.getOperator();

		switch (op) {
			case LT:
				if (l >= r) {
					stack.push((l-r)+1);
				} else {
					stack.push(0);
				}
				break;
            case LE:
                if (l > r) {
                    stack.push(l-r);
                } else {
                    stack.push(0);
                }
                break;
            case ADD:
            case OR:
            case AND:
                stack.push(l + r);
                break;
			case GT:
				if (l <= r) {
					stack.push((r-l)+1);
				} else {
					stack.push(0);
				}
				break;
			case GE:
				if (l < r) {
					stack.push(r - l);
				} else {
					stack.push(0);
				}
				break;
			case EQ:
				if (!l.equals(r)) {
					stack.push(Math.abs(l-r));
				} else {
					stack.push(0);
				}
				break;
			case NE:
				if (l.equals(r)) {
					stack.push(1);
				} else {
					stack.push(0);
				}
				break;
            case MUL:
                stack.push(l * r);
                break;
            case SUB:
                stack.push(Math.abs(Math.abs(r) - Math.abs(l)));
                break;
			default:
				stack.push(0);
				break;
		}
	}
}

class GruliaExpressionEvaluator extends Visitor {

	/*
	 * Local stack for the evaluation of the expression.
	 */
	private Stack<Object> evalStack = new Stack<Object>();

	private Map<Variable, Constant> modelMap;
	/**
	 * Public method to get the satisfiability status of the
	 * expression.
	 *
	 * @return SAT - true if the expression is satisfied,
	 *             - false otherwise
	 */
	public Boolean isSat() {
		return (Boolean) evalStack.pop();
	}

	public void setModelMap(Map<Variable, Constant> modelMap) {
	    this.modelMap = modelMap;
    }
	@Override
	public void postVisit(Expression expression) throws VisitorException {
		super.postVisit(expression);
	}

	@Override
	public void postVisit(Variable variable) throws VisitorException {
		super.postVisit(variable);
		Constant val = modelMap.get(variable);
		Integer value = -1;
		if (val == null) {
			value = 0;
		} else if (val instanceof IntConstant){
			value = ((IntConstant) val).getValue();
		} else {
			value = 0;
		}
		evalStack.push(value);
	}

	@Override
	public void postVisit(IntConstant constant) throws VisitorException {
		super.postVisit(constant);
		evalStack.push(constant.getValue());
	}

	@Override
	public void postVisit(Operation operation) throws VisitorException {
		super.postVisit(operation);

		Boolean SAT = false;
		Object l = null;
		Object r = null;

		int arity = operation.getOperator().getArity();
		if (arity == 2) {
			if (!evalStack.isEmpty()) {
				r = evalStack.pop();
			}
			if (!evalStack.isEmpty()) {
				l = evalStack.pop();
			}
		} else if (arity == 1) {
			if (!evalStack.isEmpty()) {
				l = evalStack.pop();
			}
		}

		Operation.Operator op = operation.getOperator();

		// Vars for casting
		Integer left_i, right_i;
		Boolean left_b, right_b;

		// test sat
		switch (op) {
            case LE:
                left_i = (Integer) l;
                right_i = (Integer) r;

                SAT = (left_i <= right_i);
                evalStack.push(SAT);
                break;
            case LT:
                left_i = (Integer) l;
                right_i = (Integer) r;

                SAT = (left_i < right_i);
                evalStack.push(SAT);
                break;
            case AND:
                left_b = (Boolean) l;
                right_b = (Boolean) r;

                SAT = (left_b && right_b);
                evalStack.push(SAT);
                break;
            case ADD:
                left_i = (Integer) l;
                right_i = (Integer) r;

                evalStack.push(left_i + right_i);
                break;
            case SUB:
                left_i = (Integer) l;
                right_i = (Integer) r;

                evalStack.push(left_i - right_i);
                break;
            case EQ:
                left_i = (Integer) l;
                right_i = (Integer) r;

                SAT = (left_i.equals(right_i));
                evalStack.push(SAT);
                break;
            case GE:
                left_i = (Integer) l;
                right_i = (Integer) r;

                SAT = (left_i >= right_i);
                evalStack.push(SAT);
                break;
            case GT:
                left_i = (Integer) l;
                right_i = (Integer) r;

                SAT = (left_i > right_i);
                evalStack.push(SAT);
                break;
            case MUL:
                left_i = (Integer) l;
                right_i = (Integer) r;

                evalStack.push(left_i * right_i);
                break;
            case OR:
                left_b = (Boolean) l;
                right_b = (Boolean) r;

                SAT = (left_b || right_b);
                evalStack.push(SAT);
                break;
			case NE:
				left_i = (Integer) l;
				right_i = (Integer) r;

				SAT = (!left_i.equals(right_i));
				evalStack.push(SAT);
				break;
			default:
				break;
		}
	}
}
