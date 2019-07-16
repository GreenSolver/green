package za.ac.sun.cs.green.service.z3java;

import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.service.SATService;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Z3 Java library SAT service.
 */
public class SATZ3JavaService extends SATService {

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

	/**
	 * Construct an instance of the Z3 Java library service.
	 * 
	 * @param solver     associated Green solver
	 * @param properties properties used to construct the service
	 */
	public SATZ3JavaService(Green solver, Properties properties) {
		super(solver);
		Map<String, String> cfg = new HashMap<>();
		cfg.put("model", "false");
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
		super.report(reporter);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see za.ac.sun.cs.green.service.SATService#solve(za.ac.sun.cs.green.Instance)
	 */
	@Override
	protected Boolean solve(Instance instance) {
		long startTime = System.currentTimeMillis();
		Boolean result = false;

		// translate instance to Z3
		long startTime0 = System.currentTimeMillis();
		try {
			Z3JavaTranslator translator = new Z3JavaTranslator(log, z3Context);
			instance.getExpression().accept(translator);
			int scopes = z3Solver.getNumScopes();
			if (scopes > 0) {
				z3Solver.pop(scopes);
			}
			z3Solver.push();
			z3Solver.add(translator.getTranslation());
		} catch (VisitorException x) {
			log.warn("Error in translation to Z3 ({})", x.getMessage());
		} catch (Z3Exception x) {
			log.fatal("Error in Z3 ({})", x.getMessage());
		}
		translationTimeConsumption += System.currentTimeMillis() - startTime0;

		// solve
		try {
			result = (Status.SATISFIABLE == z3Solver.check());
		} catch (Z3Exception e) {
			log.warn("Error in Z3 ({})", e.getMessage());
		}

		if (result) {
			satTimeConsumption += System.currentTimeMillis() - startTime;
		} else {
			unsatTimeConsumption += System.currentTimeMillis() - startTime;
		}
		timeConsumption += System.currentTimeMillis() - startTime;
		return result;
	}

}
