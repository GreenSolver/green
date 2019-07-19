package za.ac.sun.cs.green.service.smtlib;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Operation.Operator;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.service.ModelCoreService;
import za.ac.sun.cs.green.util.Pair;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Ancestor of model/core services that require a translation to SMTLIB.
 */
public abstract class ModelCoreSMTLIBService extends ModelCoreService {

	/**
	 * Milliseconds spent on translating to SMTLIB.
	 */
	protected long translationTimeConsumption = 0;

	/**
	 * Construct an instance of a model/core SMTLIB service.
	 *
	 * @param solver associated Green solver
	 */
	public ModelCoreSMTLIBService(Green solver) {
		super(solver);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * za.ac.sun.cs.green.service.ModelCoreService#report(za.ac.sun.cs.green.util.
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
	 * za.ac.sun.cs.green.service.ModelCoreService#modelCore(za.ac.sun.cs.green.
	 * Instance)
	 */
	@Override
	protected ModelCore modelCore(Instance instance) {
		try {
			long startTime = System.currentTimeMillis();
			SMTLIBCoreTranslator translator = new SMTLIBCoreTranslator();
			instance.getExpression().accept(translator);
			StringBuilder b = new StringBuilder();
			b.append("(set-option :produce-models true)");
			b.append("(set-option :produce-unsat-cores true)");
			b.append("(set-option :auto-config false)"); // get a smaller core
			// b.append("(set-option :relevancy 0)"); // get a smaller core
			// b.append("(set-option :solver false)"); // get a smaller core
			String logic = getLogic();
			if (logic != null) {
				b.append("(set-logic ").append(logic).append(')');
			}
			b.append(String.join(" ", translator.getVariableDefinitions()));
			b.append(String.join(" ", translator.getVariableBounds()));
			b.append(String.join(" ", translator.getAssertions()));
			// b.append("(assert ").append(translator.getTranslation()).append(')');
			b.append("(check-sat)");
			translationTimeConsumption += System.currentTimeMillis() - startTime;
			return resolve(b.toString(), translator.getVariableMap(), translator.getCoreClauseMapping());
		} catch (TranslatorUnsupportedOperation x) {
			log.fatal(x.getMessage(), x);
		} catch (VisitorException x) {
			log.fatal(x.getMessage(), x);
		}
		return null;
	}

	protected abstract ModelCore resolve(String smtQuery, Map<Variable, String> variables,
			Map<String, Expression> coreClauseMapping);

	// ======================================================================
	//
	// SPECIALIZATION OF THE SMTLIB TRANSLATOR
	//
	// ======================================================================

	private static class SMTLIBCoreTranslator extends SMTLIBTranslator {

		private static final String ASSERTION_PREFIX = "q";

		private static final String CLAUSE_PREFIX = "x";

		private int orDepth = 0;

		private int assertionCounter = 0;

		private final List<String> assertions = new LinkedList<>();

		private final Map<String, Expression> coreClauseMapping = new HashMap<>();

		public List<String> getAssertions() {
			return assertions;
		}

		public Map<String, Expression> getCoreClauseMapping() {
			return coreClauseMapping;
		}

		private String buildAssert(String name) {
			return new StringBuilder().append("(assert (! ").append(name).append(" :named ").append(CLAUSE_PREFIX)
					.append(name).append("))").toString();
		}

		private void addBound(String op1, String name, int bound, String suffix, IntVariable var, Operator op2) {
			StringBuilder b = new StringBuilder().append('(');
			b.append(op1).append(' ').append(name).append(' ');
			b.append(transformNegative(bound)).append(')');
			String boundStr = b.toString();
			b.setLength(0);
			String boundName = b.append(name).append(suffix).toString();
			Expression boundExpr = new Operation(op2, var, new IntConstant(bound));
			b.setLength(0);
			b.append("(define-const ").append(boundName).append(" Bool ");
			String boundConst = b.append(boundStr).append(')').toString();
			coreClauseMapping.put(CLAUSE_PREFIX + boundName, boundExpr);
			assertions.add(buildAssert(boundName));
			variableBounds.add(boundConst);
		}

		@Override
		public void postVisit(IntVariable variable) {
			String v = variableMap.get(variable);
			String n = variable.getName();
			if (v == null) {
				StringBuilder b = new StringBuilder();
				b.append("(declare-const ").append(n).append(" Int)");
				variableDefinitions.add(b.toString());
				addBound(">=", n, variable.getLowerBound(), "-lower", variable, Operator.GE);
				addBound("<=", n, variable.getUpperBound(), "-upper", variable, Operator.LE);
				variableMap.put(variable, n);
			}
			stack.push(new Pair<>(n, IntVariable.class));
		}

		public void preVisit(Operation operation) throws TranslatorUnsupportedOperation {
			if (operation.getOperator() == Operator.OR) {
				orDepth++;
			}
		}

		@Override
		protected void postVisitExtra(Operation operation, Operator operator, StringBuilder clause) {
			if (operator == Operator.OR) {
				orDepth--;
			}
			switch (operator) {
			case EQ:
			case NE:
			case LT:
			case LE:
			case GT:
			case GE:
			case AND:
			case OR:
				StringBuilder bb = new StringBuilder();
				String assertion = ASSERTION_PREFIX + assertionCounter++; // define assertions
				bb.append("(define-const ").append(assertion);
				bb.append(" Bool ").append(clause.toString()).append(')');
				coreClauseMapping.put(CLAUSE_PREFIX + assertion, operation);
				if (orDepth == 0) {
					assertions.add(buildAssert(assertion));
				}
				getVariableBounds().add(bb.toString());
				break;
			default:
				break;
			}
		}

	}

}
