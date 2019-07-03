package za.ac.sun.cs.green.service.z3java;

import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.RealConstant;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.service.ModelService;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Z3 Java library model service.
 */
public class ModelZ3JavaService extends ModelService {

	/**
	 * Instance of the Z3 solver.
	 */
	protected static final Solver z3Solver;

	/**
	 * Context of the Z3 solver.
	 */
	protected static final Context z3Context;

	/*
	 * Static code to initialize the static fields z3Context and z3Solver.
	 */
	static {
		Map<String, String> cfg = new HashMap<>();
		cfg.put("model", "true");
		try {
			z3Context = new Context(cfg);
		} catch (Exception x) {
			x.printStackTrace();
			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + x);
		}
		// z3Solver = z3Context.mkSolver(Z3_LOGIC);
		z3Solver = z3Context.mkSolver();
	}

	/**
	 * Milliseconds spent by this service.
	 */
	protected long timeConsumption = 0;

	/**
	 * Milliseconds used to compute a SAT result.
	 */
	protected long satTimeConsumption = 0;

	/**
	 * Milliseconds used to compute an UNSAT result.
	 */
	protected long unsatTimeConsumption = 0;

	/**
	 * Milliseconds used to translate Green expression to Z3 library calls.
	 */
	protected long translationTimeConsumption = 0;

	/**
	 * Construct an instance of the Z3 Java library service.
	 * 
	 * @param solver     associated Green solver
	 * @param properties properties used to construct the service
	 */
	public ModelZ3JavaService(Green solver, Properties properties) {
		super(solver);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see za.ac.sun.cs.green.service.SATService#report(za.ac.sun.cs.green.util.
	 * Reporter)
	 */
	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("timeConsumption", timeConsumption);
		reporter.report("  satTimeConsumption", satTimeConsumption);
		reporter.report("  unsatTimeConsumption", unsatTimeConsumption);
		reporter.report("  translationTimeConsumption", translationTimeConsumption);
		super.report(reporter);
	}

	@Override
	protected ModelService.Model model(Instance instance) {
		long startTime = System.currentTimeMillis();

		// translate instance to Z3
		long startTime0 = System.currentTimeMillis();
		Z3JavaTranslator translator = new Z3JavaTranslator(z3Context);
		try {
			instance.getExpression().accept(translator);
			z3Solver.push();
			z3Solver.add(translator.getTranslation());
		} catch (VisitorException x) {
			log.warn("Error in translation to Z3 ({})", x.getMessage());
		} catch (Z3Exception x) {
			log.fatal("Error in Z3 ({})", x.getMessage());
		}
		translationTimeConsumption += System.currentTimeMillis() - startTime0;

		// solve
		Map<Variable, Constant> results = new HashMap<>();
		try {
			if (Status.SATISFIABLE == z3Solver.check()) {
				Map<Variable, Expr> variableMap = translator.getVariableMap();
				com.microsoft.z3.Model model = z3Solver.getModel();
				for (Map.Entry<Variable, Expr> entry : variableMap.entrySet()) {
					Variable var = entry.getKey();
					Expr z3Var = entry.getValue();
					Expr z3Val = model.evaluate(z3Var, false);
					Constant val = null;
					if (z3Val.isIntNum()) {
						val = new IntConstant(Integer.parseInt(z3Val.toString()));
					} else if (z3Val.isRatNum()) {
						val = new RealConstant(Double.parseDouble(z3Val.toString()));
					} else {
						log.warn("Error unsupported type for variable {}", z3Val);
						return null;
					}
					results.put(var, val);
				}
			} else {
				unsatTimeConsumption += System.currentTimeMillis() - startTime;
				timeConsumption += System.currentTimeMillis() - startTime;
				return new ModelService.Model(false, null);
			}
		} catch (Z3Exception x) {
			log.warn("Error in Z3 ({})", x.getMessage());
		}
		satTimeConsumption += System.currentTimeMillis() - startTime;
		timeConsumption += System.currentTimeMillis() - startTime;
		return new ModelService.Model(true, results);

	}

}
