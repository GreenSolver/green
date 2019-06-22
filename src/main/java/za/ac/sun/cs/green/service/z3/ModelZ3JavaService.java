package za.ac.sun.cs.green.service.z3;

import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

import org.apache.logging.log4j.Level;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.service.ModelService;
import za.ac.sun.cs.green.util.Reporter;

public class ModelZ3JavaService extends ModelService {

	Context ctx;
	Solver z3Solver;
	private long timeConsumption = 0;
	private long satTimeConsumption = 0;
	private long unsatTimeConsumption = 0;

	public ModelZ3JavaService(Green solver, Properties properties) {
		super(solver);
		HashMap<String, String> cfg = new HashMap<String, String>();
		cfg.put("model", "true");
		try {
			ctx = new Context(cfg);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
		}
	}

	@Override
	protected Map<Variable, Object> model(Instance instance) {
		long startTime = System.currentTimeMillis();
		HashMap<Variable, Object> results = new HashMap<Variable, Object>();
		// translate instance to Z3
		Z3JavaTranslator translator = new Z3JavaTranslator(ctx);
		try {
			instance.getExpression().accept(translator);
		} catch (VisitorException e1) {
			log.log(Level.WARN, "Error in translation to Z3" + e1.getMessage());
		}
		// get context out of the translator
		BoolExpr expr = translator.getTranslation();
		// model should now be in ctx
		try {
//            System.out.println(expr.toString());
			z3Solver = ctx.mkSolver();
			z3Solver.add(expr);
		} catch (Z3Exception e1) {
			log.log(Level.WARN, "Error in Z3" + e1.getMessage());
		}
		// solve
		try { // Real Stuff is still untested
			if (Status.SATISFIABLE == z3Solver.check()) {
				Map<Variable, Expr> variableMap = translator.getVariableMap();
				Model model = z3Solver.getModel();
				for (Map.Entry<Variable, Expr> entry : variableMap.entrySet()) {
					Variable greenVar = entry.getKey();
					Expr z3Var = entry.getValue();
					Expr z3Val = model.evaluate(z3Var, false);
					Object val = null;
					if (z3Val.isIntNum()) {
						val = Integer.parseInt(z3Val.toString());
					} else if (z3Val.isRatNum()) {
						val = Double.parseDouble(z3Val.toString());
					} else {
						log.log(Level.WARN, "Error unsupported type for variable " + z3Val);
						return null;
					}
					results.put(greenVar, val);
					// String logMessage = "" + greenVar + " has value " + val;
//					log.log(Level.INFO,logMessage);
				}
			} else {
//				log.log(Level.WARNING,"constraint has no model, it is infeasible");
				long a = System.currentTimeMillis() - startTime;
				timeConsumption += a;
				unsatTimeConsumption += a;
				return null;
			}
		} catch (Z3Exception e) {
			log.log(Level.WARN, "Error in Z3" + e.getMessage());
		}
		long a = System.currentTimeMillis() - startTime;
		timeConsumption += a;
		satTimeConsumption += a;
		return results;
	}

	@Override
	public void report(Reporter reporter) {
		reporter.report(getClass().getSimpleName(), "timeConsumption = " + timeConsumption);
		reporter.report(getClass().getSimpleName(), "satTimeConsumption = " + satTimeConsumption);
		reporter.report(getClass().getSimpleName(), "unsatTimeConsumption = " + unsatTimeConsumption);
	}

}
