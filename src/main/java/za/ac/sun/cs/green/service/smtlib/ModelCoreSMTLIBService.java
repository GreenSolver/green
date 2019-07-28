/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
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
import za.ac.sun.cs.green.service.ModelCoreService.ModelCore;
import za.ac.sun.cs.green.util.Pair;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Ancestor of model/core services that require a translation to SMTLIB.
 */
public abstract class ModelCoreSMTLIBService extends ModelCoreService {

	// ======================================================================
	//
	// TIME CONSUMPTION
	//
	// ======================================================================

	/**
	 * Milliseconds spent on translating to SMTLIB.
	 */
	protected long translationTimeConsumption = 0;

	// ======================================================================
	//
	// CONSTRUCTOR & METHODS
	//
	// ======================================================================

	/**
	 * Construct an instance of a model/core SMTLIB service.
	 *
	 * @param solver
	 *               associated Green solver
	 */
	public ModelCoreSMTLIBService(Green solver) {
		super(solver);
	}

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

	/**
	 * Do the actual work to compute a model or a core for a Green instance. This
	 * should return a {@link ModelCore} that contains a flag to indicate the
	 * satisfiability of an expression and a model (if it is satisfiable) or an
	 * unsatisfiable core (if it is unsatisfiable). The method may also return
	 * {@code null} if no answer can be determined.
	 * 
	 * @param smtQuery
	 *                          query (expression) in SMTLIB format
	 * @param variables
	 *                          mapping from variables to variable names
	 * @param coreClauseMapping
	 * @return a {@link ModelCore} or {@code null} if no answer can be determined
	 */
	protected abstract ModelCore resolve(String smtQuery, Map<Variable, String> variables,
			Map<String, Expression> coreClauseMapping);

	// ======================================================================
	//
	// SPECIALIZATION OF THE SMTLIB TRANSLATOR
	//
	// ======================================================================

	/**
	 * Refinement of {@link SMTLIBTranslator} that adds a mapping for computing
	 * cores.
	 */
	private static class SMTLIBCoreTranslator extends SMTLIBTranslator {

		/**
		 * Prefix for assertion names.
		 */
		private static final String ASSERTION_PREFIX = "q";

		/**
		 * Prefix for clause names.
		 */
		private static final String CLAUSE_PREFIX = "x";

		/**
		 * Inside how many OR operations is the current expression?
		 */
		private int orDepth = 0;

		/**
		 * How many assertions have been generated?
		 */
		private int assertionCounter = 0;

		/**
		 * List of generated assertions. Each assertion is an SMTLIB2 expression (as a
		 * string) that comprises one or more clauses. An example of a two-clause
		 * assertion is "{@code (x==1)||(y==2)}", which consists of the two clauses
		 * "{@code x==1}" and "{@code y==2}".
		 */
		private final List<String> assertions = new LinkedList<>();

		/**
		 * Mapping from clause names to clauses. A clause is a predicate (such as
		 * "{@code z>5}") or a boolean combination of other clauses.
		 */
		private final Map<String, Expression> coreClauseMapping = new HashMap<>();

		/**
		 * Return the list of generated assertions.
		 *
		 * @return list of assertions
		 */
		public List<String> getAssertions() {
			return assertions;
		}

		/**
		 * Return the name-clause mapping.
		 *
		 * @return mapping from clause names to clauses
		 */
		public Map<String, Expression> getCoreClauseMapping() {
			return coreClauseMapping;
		}

		/**
		 * Generate the SMTLIB2 expression for an assertion.
		 *
		 * @param name
		 *             name of the assertion
		 * @return resulting clause as an SMTLIB2 string
		 */
		private String buildAssert(String name) {
			return new StringBuilder().append("(assert (! ").append(name).append(" :named ").append(CLAUSE_PREFIX)
					.append(name).append("))").toString();
		}

		/**
		 * Add a lower or upper bound for a variable. The bound is added as a clause to
		 * the {@link #coreClauseMapping} mapping, as an assertion to the
		 * {@link #assertions} list, and to the inherited {@link #variableBounds} set.
		 * 
		 * @param bound
		 *               the lower or upper bound
		 * @param suffix
		 *               a string suffix to identify if this is a lower or upper bound,
		 *               appended to bound assertion name
		 * @param var
		 *               GREEN representation of variable
		 * @param op
		 *               GREEN representation of bound operator
		 */
		private void addBound(int bound, String suffix, IntVariable var, Operator op) {
			String nam = var.getName();
			StringBuilder b = new StringBuilder().append('(');
			b.append(op.toString()).append(' ').append(nam).append(' ');
			b.append(transformNegative(bound)).append(')');
			String boundStr = b.toString();
			b.setLength(0);
			String boundName = b.append(nam).append(suffix).toString();
			Expression boundExpr = new Operation(op, var, new IntConstant(bound));
			b.setLength(0);
			b.append("(define-const ").append(boundName).append(" Bool ");
			String boundConst = b.append(boundStr).append(')').toString();
			coreClauseMapping.put(CLAUSE_PREFIX + boundName, boundExpr);
			assertions.add(buildAssert(boundName));
			variableBounds.add(boundConst);
		}

		/**
		 * Generate the definition for a variable (if new) and add lower-bound and
		 * upper-bound assertions for the variable.
		 *
		 * @param variable
		 *                 variable to process
		 *
		 * @see za.ac.sun.cs.green.service.smtlib.SMTLIBTranslator#postVisit(za.ac.sun.cs.green.expr.IntVariable)
		 */
		@Override
		public void postVisit(IntVariable variable) {
			String v = variableMap.get(variable);
			String n = variable.getName();
			if (v == null) {
				StringBuilder b = new StringBuilder();
				b.append("(declare-const ").append(n).append(" Int)");
				variableDefinitions.add(b.toString());
				addBound(variable.getLowerBound(), "-lower", variable, Operator.GE);
				addBound(variable.getUpperBound(), "-upper", variable, Operator.LE);
				variableMap.put(variable, n);
			}
			stack.push(new Pair<>(n, IntVariable.class));
		}

		/**
		 * Handle an OR-operation.
		 *
		 * @param operation
		 *                  operation to process
		 * @throws TranslatorUnsupportedOperation
		 *                                        never
		 *
		 * @see za.ac.sun.cs.green.expr.Visitor#preVisit(za.ac.sun.cs.green.expr.Operation)
		 */
		@Override
		public void preVisit(Operation operation) throws TranslatorUnsupportedOperation {
			if (operation.getOperator() == Operator.OR) {
				orDepth++;
			}
		}

		/**
		 * Handle an operation by creating a clause (and adding it to the
		 * {@link #coreClauseMapping}) and potentially creating an asserting (and adding
		 * it to the {@link #assertions} list if outside an OR-operation).
		 *
		 * @param operation
		 *                  operation to process
		 * @param clause
		 *                  unused partial clause being constructed for operation
		 * @param type
		 *                  unused type of the operation
		 *
		 * @see za.ac.sun.cs.green.service.smtlib.SMTLIBTranslator#postVisitExtra(za.ac.sun.cs.green.expr.Operation,
		 *      java.lang.StringBuilder, java.lang.Class)
		 */
		@Override
		protected void postVisitExtra(Operation operation, StringBuilder clause, Class<? extends Variable> type) {
			Operator operator = operation.getOperator();
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
