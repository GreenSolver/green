package za.ac.sun.cs.green.service.z3java;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Properties;
import java.util.Set;

import org.apache.logging.log4j.Level;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Model;
//import com.microsoft.z3.RatNum;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.RealConstant;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.service.ModelCoreService;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Z3 Java library model service.
 */
public class ModelCoreZ3JavaService extends ModelCoreService {

	/**
	 * Logic used for the Z3 solver.
	 */
	protected static final String Z3_LOGIC = "QF_LIA";

	/**
	 * Instance of the Z3 solver.
	 */
	protected final Solver z3Solver;

	/**
	 * Context of the Z3 solver.
	 */
	protected final Context z3Context;

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

	protected int conjunctCount = 0;
	protected int variableCount = 0;

	/**
	 * Construct an instance of the Z3 Java library service.
	 * 
	 * @param solver     associated Green solver
	 * @param properties properties used to construct the service
	 */
	public ModelCoreZ3JavaService(Green solver, Properties properties) {
		super(solver);
		Map<String, String> cfg = new HashMap<>();
		cfg.put("model", "true");
		cfg.put("unsat_core", "true");
		cfg.put("auto_config", "false");
		try {
			z3Context = new Context(cfg);
		} catch (Exception x) {
			x.printStackTrace();
			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + x);
		}
		z3Solver = z3Context.mkSolver(Z3_LOGIC);
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
//		reporter.report("conjunctCount", conjunctCount);
//		reporter.report("variableCount", variableCount);
		super.report(reporter);
	}

	@Override
	protected ModelCore modelCore(Instance instance) {
		long startTime = System.currentTimeMillis();

		// translate instance to Z3
		long startTime0 = System.currentTimeMillis();
		Z3JavaTranslator translator = new Z3JavaTranslator(log, z3Context);
		log.debug("translating: {}", () -> instance.getExpression());
		try {
			instance.getExpression().accept(translator);
		} catch (VisitorException x) {
			log.warn("Error in translation to Z3 ({})", x.getMessage());
		} catch (Z3Exception x) {
			log.fatal("Error in Z3 ({})", x.getMessage());
		}
		translationTimeConsumption += System.currentTimeMillis() - startTime0;

		// solve & extract model/core
		Map<BoolExpr, Expression> coreClauseMappings = translator.getCoreClauseMappings();
		try {
			z3Solver.reset();
			for (BoolExpr core : coreClauseMappings.keySet()) {
				BoolExpr boolExpr = translator.getAssertions().get(coreClauseMappings.get(core));
				log.debug("assertion: {}", boolExpr);
				z3Solver.assertAndTrack(boolExpr, core);
			}
		} catch (Z3Exception e1) {
			log.log(Level.WARN, "Error in Z3" + e1.getMessage());
		}
		Map<Variable, Constant> model = new HashMap<>();
		try {
			if (Status.SATISFIABLE == z3Solver.check()) {
				Map<Variable, Expr> variableMap = translator.getVariableMap();
				Model z3Model = z3Solver.getModel();
				for (Map.Entry<Variable, Expr> entry : variableMap.entrySet()) {
					Variable var = entry.getKey();
					Expr z3Var = entry.getValue();
					Expr z3Val = z3Model.evaluate(z3Var, false);
					Constant val = null;
					if (z3Val.isIntNum()) {
						val = new IntConstant(Integer.parseInt(z3Val.toString()));
					} else if (z3Val.isRatNum()) {
//						RatNum rat = (RatNum) z3Val;
//						val = new RealConstant(rat.getNumerator().getInt64() * 1.0 / rat.getDenominator().getInt64());
//					} else if (z3Val.isReal()) {
//						val = new RealConstant(Double.parseDouble(z3Val.toString()));
						String z3ValString = z3Val.toString();
						if (z3ValString.contains("/")) {
							String[] rat = z3ValString.split("/");
							double num = Double.parseDouble(rat[0]);
							double den = Double.parseDouble(rat[1]);
							val = new RealConstant(num / den);
						} else {
							val = new RealConstant(Double.parseDouble(z3ValString));
						}
					} else {
						log.warn("Error unsupported type for variable {}", z3Val);
						return null;
					}
					model.put(var, val);
				}
			} else {
				Set<Expression> unsatCore = new HashSet<>();
				for (BoolExpr core : z3Solver.getUnsatCore()) {
					if (core != null) {
						Expression clause = coreClauseMappings.get(core);
						if (clause != null) {
							unsatCore.add(clause);
						}
					}
				}
				unsatTimeConsumption += System.currentTimeMillis() - startTime;
				timeConsumption += System.currentTimeMillis() - startTime;
				return new ModelCore(false, null, unsatCore);
			}
		} catch (Z3Exception e) {
			log.log(Level.WARN, "Error in Z3" + e.getMessage());
		}
		satTimeConsumption += System.currentTimeMillis() - startTime;
		timeConsumption += System.currentTimeMillis() - startTime;
		return new ModelCore(true, model, null);
	}

}
