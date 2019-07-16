package za.ac.sun.cs.green.service.smtlib;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import za.ac.sun.cs.green.expr.BoolVariable;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.RealConstant;
import za.ac.sun.cs.green.expr.RealVariable;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.Operation.Operator;
import za.ac.sun.cs.green.util.Pair;

/**
 * Visitor to translate a GREEN expression to an SMTLIB expression.
 */
public class SMTLIBTranslator extends Visitor {

	/**
	 * Stack of operands.
	 */
	protected final Stack<Pair<String, Class<? extends Variable>>> stack = new Stack<>();

	/**
	 * Mapping from variables to variable names.
	 */
	protected final Map<Variable, String> variableMap = new HashMap<Variable, String>();

	/**
	 * List of SMTLIB variable definitions.
	 */
	protected final List<String> variableDefinitions = new LinkedList<String>();

	/**
	 * List of variable lower and upper bounds as SMTLIB assertions.
	 */
	protected final List<String> variableBounds = new LinkedList<String>();

	/**
	 * Return the variable/name mapping.
	 * 
	 * @return variable/name mapping
	 */
	public Map<Variable, String> getVariableMap() {
		return variableMap;
	}

	/**
	 * Return the list of SMTLIB variable definitions.
	 * 
	 * @return list of SMTLIB variable definitions
	 */
	public List<String> getVariableDefinitions() {
		return variableDefinitions;
	}

	/**
	 * Return the list of SMTLIB variable bounds.
	 * 
	 * @return list of SMTLIB variable bounds
	 */
	public List<String> getVariableBounds() {
		return variableBounds;
	}

	/**
	 * Return the SMTLIB translation of an expression as an SMTLIB string. This
	 * includes the variable bounds.
	 * 
	 * @return SMTLIB translation
	 */
	public String getTranslation() {
		StringBuilder b = new StringBuilder();
		b.append("(and");
		for (String bound : variableBounds) {
			b.append(' ').append(bound);
		}
		Pair<String, Class<? extends Variable>> translation = stack.pop();
		b.append(' ').append(translation.getL()).append(')');
		assert stack.isEmpty();
		return b.toString();
	}

	/**
	 * Translate a negative integral literal to its SMTLIB equivalent. For example,
	 * "{@code -5}" is translated to
	 * 
	 * <pre>
	 * (-5)
	 * </pre>
	 * 
	 * Note that positive parameters are returned as strings.
	 * 
	 * @param v integer literal
	 * @return the SMTLIB equivalent
	 */
	protected String transformNegative(long v) {
		if (v < 0) {
			StringBuilder b = new StringBuilder();
			b.append("(- ").append(-v).append(')');
			return b.toString();
		} else {
			return Long.toString(v);
		}
	}

	/**
	 * Translate a negative real literal to its SMTLIB equivalent. For example,
	 * "{@code -5.3}" is translated to
	 * 
	 * <pre>
	 * (-5.3)
	 * </pre>
	 * 
	 * Note that positive parameters are returned as strings.
	 * 
	 * @param v real literal
	 * @return the SMTLIB equivalent
	 */
	protected String transformNegative(double v) {
		if (v < 0) {
			StringBuilder b = new StringBuilder();
			b.append("(- ").append(-v).append(')');
			return b.toString();
		} else {
			return Double.toString(v);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.
	 * IntConstant)
	 */
	@Override
	public void postVisit(IntConstant constant) {
		int value = constant.getValue();
		stack.push(new Pair<>(transformNegative(value), IntVariable.class));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.
	 * RealConstant)
	 */
	@Override
	public void postVisit(RealConstant constant) {
		double value = constant.getValue();
		stack.push(new Pair<>(transformNegative(value), RealVariable.class));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.
	 * IntVariable)
	 */
	@Override
	public void postVisit(IntVariable variable) {
		String v = variableMap.get(variable);
		String n = variable.getName();
		if (v == null) {
			StringBuilder b = new StringBuilder();
			b.append("(declare-fun ").append(n).append(" () Int)");
			variableDefinitions.add(b.toString());

			// lower bound
			b.setLength(0);
			b.append("(and (>= ").append(n).append(' ');
			b.append(transformNegative(variable.getLowerBound()));
			// upper bound
			b.append(") (<= ").append(n).append(' ');
			b.append(transformNegative(variable.getUpperBound()));
			b.append("))");

			variableBounds.add(b.toString());
			variableMap.put(variable, n);
		}
		stack.push(new Pair<>(n, IntVariable.class));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.
	 * RealVariable)
	 */
	@Override
	public void postVisit(RealVariable variable) {
		String v = variableMap.get(variable);
		String n = variable.getName();
		if (v == null) {
			StringBuilder b = new StringBuilder();
			b.append("(declare-fun ").append(n).append(" () Real)");
			variableDefinitions.add(b.toString());
			b.setLength(0);
			// lower bound
			b.append("(and (>= ").append(n).append(' ');
			b.append(transformNegative(variable.getLowerBound()));
			// upper bound
			b.append(") (<= ").append(n).append(' ');
			b.append(transformNegative(variable.getUpperBound()));
			// end
			b.append("))");
			variableBounds.add(b.toString());
			variableMap.put(variable, n);
		}
		stack.push(new Pair<>(n, RealVariable.class));
	}

	/**
	 * Determine the supertype of two terms. This is the "least" type that both the
	 * terms belong to.
	 * 
	 * @param left  first term
	 * @param right second term
	 * @return least type that contains both terms
	 */
	protected Class<? extends Variable> superType(Pair<String, Class<? extends Variable>> left,
			Pair<String, Class<? extends Variable>> right) {
		if ((left.getR() == RealVariable.class) || (right.getR() == RealVariable.class)) {
			return RealVariable.class;
		} else if ((left.getR() == BoolVariable.class) || (right.getR() == BoolVariable.class)) {
			return BoolVariable.class;
		} else {
			return IntVariable.class;
		}
	}

	/**
	 * Return the SMTLIB translation of a term such that it is compatible with the
	 * type of a second operand.
	 * 
	 * @param term term to translate
	 * @param type type required for other operand
	 * @return SMTLIB translation of term
	 */
	protected String adjust(Pair<String, Class<? extends Variable>> term, Class<? extends Variable> type) {
		String s = term.getL();
		Class<? extends Variable> t = term.getR();
		if (t == type) {
			return s;
		} else {
			StringBuilder b = new StringBuilder();
			b.append("(to_real ").append(s).append(')');
			return b.toString();
		}
	}

	/**
	 * Map GREEN operators to their SMTLIB equivalent.
	 * 
	 * @param op GREEN operator
	 * @return the SMTLIB operator
	 * @throws TranslatorUnsupportedOperation if an operator cannot/should not be
	 *                                        translated
	 */
	protected String setOperator(Operator op) throws TranslatorUnsupportedOperation {
		switch (op) {
		case EQ:
			return "=";
		case LT:
			return "<";
		case LE:
			return "<=";
		case GT:
			return ">";
		case GE:
			return ">=";
		case AND:
			return "and";
		case OR:
			return "or";
		case IMPLIES:
			return "=>"; // not sure about this one?
		case ADD:
			return "+";
		case SUB:
			return "-";
		case MUL:
			return "*";
		case DIV:
			return "div";
		case MOD:
			return "mod";
		default:
			throw new TranslatorUnsupportedOperation("unsupported operation " + op);
		}
	}

	/**
	 * Map GREEN operators to their resulting type.
	 * 
	 * @param op GREEN operator
	 * @param supertype least common parent type
	 * @return resulting type
	 * @throws TranslatorUnsupportedOperation if an operator cannot/should not be
	 *                                        translated
	 */
	protected Class<? extends Variable> setType(Operator op, Class<? extends Variable> supertype) throws TranslatorUnsupportedOperation {
		switch (op) {
		case EQ:
		case NE:
		case LT:
		case LE:
		case GT:
		case GE:
		case AND:
		case OR:
		case IMPLIES:
			return BoolVariable.class;
		case ADD:
		case SUB:
		case MUL:
		case DIV:
		case MOD:
			return supertype;
		default:
			throw new TranslatorUnsupportedOperation("unsupported operation " + op);
		}
	}
	
	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.Operation)
	 */
	public void postVisit(Operation operation) throws TranslatorUnsupportedOperation {
		Pair<String, Class<? extends Variable>> l = null;
		Pair<String, Class<? extends Variable>> r = null;
		Operator op = operation.getOperator();
		int arity = op.getArity();
		if (arity == 2) {
			if (!stack.isEmpty()) {
				r = stack.pop();
			}
			if (!stack.isEmpty()) {
				l = stack.pop();
			}
		} else if (arity == 1) {
			if (!stack.isEmpty()) {
				l = stack.pop();
			}
		}
		Class<? extends Variable> v = superType(l, r);
		StringBuilder b = new StringBuilder();
		if (op.equals(Operator.NE)) {
			b.append("(not (= ");
			b.append(adjust(l, v)).append(' ');
			b.append(adjust(r, v)).append("))");
		} else {
			b.append('(').append(setOperator(op)).append(' ');
			b.append(adjust(l, v)).append(' ');
			b.append(adjust(r, v)).append(')');
		}
		stack.push(new Pair<>(b.toString(), setType(op, v)));
		postVisitExtra(operation, op, b);
	}

	protected void postVisitExtra(Operation operation, Operator operator, StringBuilder clause) {
		// default is empty
	}

}
