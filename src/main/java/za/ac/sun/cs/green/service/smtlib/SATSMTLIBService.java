package za.ac.sun.cs.green.service.smtlib;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.service.SATService;
import za.ac.sun.cs.green.util.Misc;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Ancestor of SAT services that require a translation to SMTLIB.
 */
public abstract class SATSMTLIBService extends SATService {

	/**
	 * Number of conjuncts that appear in the translated expression.
	 */
	protected int conjunctCount = 0;

	/**
	 * Number of variables that appear in the translated expression.
	 */
	protected int varCount = 0;

	/**
	 * Milliseconds spent on translating to SMTLIB.
	 */
	protected long translationTimeConsumption = 0;

	/**
	 * Construct an instance of a SAT SMTLIB service.
	 *
	 * @param solver associated Green solver
	 */
	public SATSMTLIBService(Green solver) {
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
		reporter.report("conjunctCount", conjunctCount);
		reporter.report("varCount", varCount);
		reporter.report("translationTimeConsumption", translationTimeConsumption);
		super.report(reporter);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see za.ac.sun.cs.green.service.SATService#solve(za.ac.sun.cs.green.Instance)
	 */
	@Override
	protected Boolean solve(Instance instance) {
		try {
			long startTime = System.currentTimeMillis();
			SMTLIBTranslator translator = new SMTLIBTranslator();
			instance.getExpression().accept(translator);
			StringBuilder b = new StringBuilder();
			b.append("(set-option :produce-models false)");
			b.append("(set-logic QF_LIA)");
			b.append(Misc.join(translator.getVariableDefinitions(), " "));
			b.append("(assert ").append(translator.getTranslation()).append(')');
			b.append("(check-sat)");
			String translation = b.toString();
			conjunctCount += instance.getExpression().toString().split("&&").length;
			varCount += translator.getVariableDefinitions().size();
			translationTimeConsumption += System.currentTimeMillis() - startTime;
			return resolve(translation);
		} catch (TranslatorUnsupportedOperation x) {
			log.fatal(x.getMessage(), x);
		} catch (VisitorException x) {
			log.fatal(x.getMessage(), x);
		}
		return null;
	}

	/**
	 * Do the actual work to solve a Green instance. This should return a
	 * {@link Boolean} to indicate that the expression is satisfiable ({@code true})
	 * or unsatisfiable ({@code false}), or {@code null} if no answer can be
	 * determined.
	 * 
	 * @param smtQuery query (expression) in SMTLIB format
	 * @return a {@link Boolean} to indicate satisfiability of the expression, or
	 *         {@code null} if no answer can be determined
	 */
	protected abstract Boolean resolve(String smtQuery);

}
