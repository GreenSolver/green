package za.ac.sun.cs.green.service.z3;

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

public class ModelCoreZ3JavaService extends ModelCoreService {

	Context ctx;
	Solver z3Solver;
	protected long timeConsumption = 0;
	protected long translationTimeConsumption = 0;
	protected long satTimeConsumption = 0;
	protected long unsatTimeConsumption = 0;
	protected int conjunctCount = 0;
	protected int variableCount = 0;
	private static final String LOGIC = "QF_LIA";

	private static final class Z3Wrapper {
		private Context ctx;
		private Solver solver;

		private static Z3Wrapper instance = null;

		public static Z3Wrapper getInstance() {
			if (instance == null) {
				instance = new Z3Wrapper();
			}
			return instance;
		}

		private Z3Wrapper() {
			HashMap<String, String> cfg = new HashMap<String, String>();
			cfg.put("model", "true");
			cfg.put("unsat_core", "true");
			cfg.put("auto_config", "false");

			try {
				ctx = new Context(cfg);
			} catch (Exception e) {
				e.printStackTrace();
				throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
			}
			// TODO : Changed logic to QF_LIA from AUF_LIA
//            solver = ctx.mkSolver(LOGIC); // removed since this creation is unnecessary
		}

		public Solver getSolver() {
			return this.solver;
		}

		public Context getCtx() {
			return this.ctx;
		}
	}

	public ModelCoreZ3JavaService(Green solver, Properties properties) {
		super(solver);
		Z3Wrapper z3Wrapper = Z3Wrapper.getInstance();
		z3Solver = z3Wrapper.getSolver();
		ctx = z3Wrapper.getCtx();
	}

	@Override
	protected ModelCore modelCore(Instance instance) {
		long startTime = System.currentTimeMillis();
		ModelCore mc = null;
		// translate instance to Z3
		long t0Translation = System.currentTimeMillis();
		Z3JavaTranslator translator = new Z3JavaTranslator(ctx);
		try {
			instance.getExpression().accept(translator);
		} catch (VisitorException e1) {
			log.log(Level.WARN, "Error in translation to Z3" + e1.getMessage());
		}
		// get context out of the translator
		Map<BoolExpr, Expression> namedAsserts = translator.getCoreMappings();
		// model should now be in ctx
		try {
			z3Solver = ctx.mkSolver(LOGIC); // create clean instance
			for (BoolExpr px : namedAsserts.keySet()) {
				// px is the Predicate name
				// assert and track each predicate/assertion
				z3Solver.assertAndTrack(translator.getAsserts().get(namedAsserts.get(px)), px);
			}
		} catch (Z3Exception e1) {
			log.log(Level.WARN, "Error in Z3" + e1.getMessage());
		}
//		conjunctCount += instance.getExpression().getString().split("&&").length;
		conjunctCount += instance.getExpression().toString().split("&&").length;
		variableCount += translator.getVariableCount();
		translationTimeConsumption += (System.currentTimeMillis() - t0Translation);
		// solve
		try { // Real Stuff is still untested
			if (Status.SATISFIABLE == z3Solver.check()) {
				Map<Variable, Expr> variableMap = translator.getVariableMap();
				HashMap<Variable, Constant> greenModel = new HashMap<>();
				Model model = z3Solver.getModel();
				for (Map.Entry<Variable, Expr> entry : variableMap.entrySet()) {
					Variable greenVar = entry.getKey();
					Expr z3Var = entry.getValue();
					Expr z3Val = model.evaluate(z3Var, false);
					Constant val = null;
					if (z3Val.isIntNum()) {
						val = new IntConstant(Integer.parseInt(z3Val.toString()));
					} else if (z3Val.isRatNum()) {
						val = new RealConstant(Double.parseDouble(z3Val.toString()));
					} else if (z3Val.isBV()) {
						val = new IntConstant((int) Long.parseLong(z3Val.toString()));
					} else {
						log.log(Level.WARN, "Error unsupported type for variable " + z3Val);
						return null;
					}
					greenModel.put(greenVar, val);
//					log.log(Level.INFO,"" + greenVar + " has value " + val);
				}
				mc = new ModelCore(true, greenModel, null);
				satCount++;
				satTimeConsumption += (System.currentTimeMillis() - startTime);
			} else {
//				log.log(Level.WARNING,"constraint has no model, it is infeasible");
				Set<Expression> clauses = new HashSet<>();
				for (Expr tmp : z3Solver.getUnsatCore()) {
					if (tmp != null) {
						Expression realClause = namedAsserts.get(tmp);
						if (realClause != null) {
							clauses.add(realClause);
						}
					}
				}
				mc = new ModelCore(false, null, clauses);
				unsatCount++;
				unsatTimeConsumption += (System.currentTimeMillis() - startTime);
			}
		} catch (Z3Exception e) {
			log.log(Level.WARN, "Error in Z3" + e.getMessage());
		}
		timeConsumption += (System.currentTimeMillis() - startTime);
		return mc;
	}

	@Override
	public void report(Reporter reporter) {
//        reporter.reportZZ("cacheHitCount", cacheHitCount);
//        reporter.reportZZ("cacheMissCount", cacheMissCount);
//        reporter.reportZZ("satCacheHitCount", modelHitCount);
//        reporter.reportZZ("unsatCacheHitCount", noModelHitCount);
//        reporter.reportZZ("satCacheMissCount", modelMissCount);
//        reporter.reportZZ("unsatCacheMissCount", noModelMissCount);
//        reporter.reportZZ("satQueries", modelCount);
//        reporter.reportZZ("unsatQueries", noModelCount);
		reporter.setContext(getClass().getSimpleName());
		reporter.report("timeConsumption", timeConsumption);
		reporter.report("satTimeConsumption", satTimeConsumption);
		reporter.report("unsatTimeConsumption", unsatTimeConsumption);
		reporter.report("translationTimeConsumption", translationTimeConsumption);
		reporter.report("conjunctCount", conjunctCount);
		reporter.report("variableCount", variableCount);
	}

}
