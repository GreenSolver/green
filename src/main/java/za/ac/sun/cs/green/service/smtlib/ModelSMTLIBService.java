package za.ac.sun.cs.green.service.smtlib;

import java.util.Map;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.service.ModelService;
import za.ac.sun.cs.green.util.Misc;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Ancestor of model services that require a translation to SMTLIB.
 */
public abstract class ModelSMTLIBService extends ModelService {

	/**
	 * Milliseconds spent on translating to SMTLIB.
	 */
	protected long translationTimeConsumption = 0;

	/**
	 * Construct an instance of a model SMTLIB service.
	 *
	 * @param solver associated Green solver
	 */
	public ModelSMTLIBService(Green solver) {
		super(solver);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see za.ac.sun.cs.green.service.ModelService#report(za.ac.sun.cs.green.util.
	 * Reporter)
	 */
	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("translationTimeConsumption", translationTimeConsumption);
		super.report(reporter);
	}

	/**
	 * Return the logic to be used for the solver. The default is to return
	 * "{@code QF_LIA}" for linear integer arithmetic.
	 *
	 * @return solver logic
	 */
	protected String getLogic() {
		return "QF_LIA";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * za.ac.sun.cs.green.service.ModelService#model(za.ac.sun.cs.green.Instance)
	 */
	@Override
	protected Model model(Instance instance) {
		try {
			long startTime = System.currentTimeMillis();
			SMTLIBTranslator translator = new SMTLIBTranslator();
			instance.getExpression().accept(translator);
			StringBuilder b = new StringBuilder();
			b.append("(set-option :produce-models true)");
			String logic = getLogic();
			if (logic != null) {
				b.append("(set-logic ").append(logic).append(')');
			}
			b.append(Misc.join(translator.getVariableDefinitions(), " "));
			b.append("(assert ").append(translator.getTranslation()).append(')');
			b.append("(check-sat)");
			translationTimeConsumption += System.currentTimeMillis() - startTime;
			return resolve(b.toString(), translator.getVariableMap());
		} catch (TranslatorUnsupportedOperation x) {
			log.fatal(x.getMessage(), x);
		} catch (VisitorException x) {
			log.fatal(x.getMessage(), x);
		}
		return null;
	}

	/**
	 * Do the actual work to solve a Green instance. This should return a
	 * {@link Model} that contains a flag to indicate the satisfiability of an
	 * expression and, if it is satisfiable, a model.
	 * 
	 * @param smtQuery  query (expression) in SMTLIB format
	 * @param variables mapping from variables to variable names
	 * @return a {@link Model} or {@code null} if no answer can be determined
	 */
	protected abstract Model resolve(String smtQuery, Map<Variable, String> variables);

}
