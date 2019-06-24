package za.ac.sun.cs.green.service.z3;

import java.util.HashMap;
import java.util.Properties;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.service.SATService;
import za.ac.sun.cs.green.util.Reporter;

public class SATZ3JavaService extends SATService {

	Context ctx;
	Solver z3Solver;
	protected long timeConsumption = 0;
	protected long translationTimeConsumption = 0;
	protected long satTimeConsumption = 0;
	protected long unsatTimeConsumption = 0;
	protected int conjunctCount = 0;
	protected int variableCount = 0;

	private static final class Z3Wrapper {
		private Context ctx;
		private Solver solver;
		private final String logic = "QF_LIA";

		private static Z3Wrapper instance = null;

		public static Z3Wrapper getInstance() {
			if (instance == null) {
				instance = new Z3Wrapper();
			}
			return instance;
		}

		private Z3Wrapper() {
			HashMap<String, String> cfg = new HashMap<String, String>();
			cfg.put("model", "false"); // "true" ?
			try {
				ctx = new Context(cfg);
			} catch (Exception e) {
				e.printStackTrace();
				throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
			}
			// TODO : Changed logic to QF_LIA from AUF_LIA
			solver = ctx.mkSolver(logic);
		}

		public Solver getSolver() {
			return this.solver;
		}

		public Context getCtx() {
			return this.ctx;
		}
	}

	public SATZ3JavaService(Green solver, Properties properties) {
		super(solver);

		Z3Wrapper z3Wrapper = Z3Wrapper.getInstance();
		z3Solver = z3Wrapper.getSolver();
		ctx = z3Wrapper.getCtx();

		/*
		 * HashMap<String, String> cfg = new HashMap<String, String>(); cfg.put("model",
		 * "false"); try{ ctx = new Context(cfg); } catch (Exception e) {
		 * e.printStackTrace(); throw new
		 * RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e); }
		 */
	}

	@Override
	protected Boolean solve(Instance instance) {
		long start = System.currentTimeMillis();
		Boolean result = false;
		// translate instance to Z3
		long t0Translation = System.currentTimeMillis();
		Z3JavaTranslator translator = new Z3JavaTranslator(ctx);
		try {
			instance.getExpression().accept(translator);
		} catch (VisitorException e1) {
			log.warn("Error in translation to Z3 ({})", e1.getMessage());
		}
		// get context out of the translator
		BoolExpr expr = translator.getTranslation();
		// model should now be in ctx
		try {
			// Z3solver = ctx.mkSolver();
			z3Solver.push();
			z3Solver.add(expr);
		} catch (Z3Exception e1) {
			log.warn("Error in Z3 ({})", e1.getMessage());
		}
//		conjunctCount += instance.getExpression().getString().split("&&").length;
		conjunctCount += instance.getExpression().toString().split("&&").length;
		variableCount += translator.getVariableCount();
		translationTimeConsumption += (System.currentTimeMillis() - t0Translation);
		// solve
		try {
			result = Status.SATISFIABLE == z3Solver.check();
		} catch (Z3Exception e) {
			log.warn("Error in Z3 ({})", e.getMessage());
		}
		// clean up
		int scopes = z3Solver.getNumScopes();
		if (scopes > 0) {
			z3Solver.pop(scopes);
		}
		timeConsumption += (System.currentTimeMillis() - start);
		if (result) {
			satTimeConsumption += (System.currentTimeMillis() - start);
		} else {
			unsatTimeConsumption += (System.currentTimeMillis() - start);
		}
		return result;
	}

	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("cacheHitCount", cacheHitCount);
		reporter.report("cacheMissCount", cacheMissCount);
		reporter.report("satCacheHitCount", satHitCount);
		reporter.report("unsatCacheHitCount", unsatHitCount);
		reporter.report("satCacheMissCount", satMissCount);
		reporter.report("unsatCacheMissCount", unsatMissCount);
		reporter.report("satQueries", satCount);
		reporter.report("unsatQueries", unsatCount);
		reporter.report("timeConsumption", timeConsumption);
		reporter.report("satTimeConsumption", satTimeConsumption);
		reporter.report("unsatTimeConsumption", unsatTimeConsumption);
		reporter.report("storageTimeConsumption", storageTimeConsumption);
		reporter.report("translationTimeConsumption", translationTimeConsumption);
		reporter.report("conjunctCount", conjunctCount);
		reporter.report("variableCount", variableCount);
	}

}
