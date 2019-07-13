package za.ac.sun.cs.green.service.choco4;

import java.util.Map;
import java.util.Stack;
import java.util.function.BiFunction;

import org.chocosolver.solver.Model;
import org.chocosolver.solver.expression.discrete.arithmetic.ArExpression;
import org.chocosolver.solver.expression.discrete.relational.ReExpression;
import org.chocosolver.solver.variables.IntVar;

import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;

public class ChocoTranslator extends Visitor {

	private final Model chocoModel;

	private final Object placeholder = new Object();

	private final Stack<Object> stack = new Stack<Object>();

	private final Map<Variable, IntVar> variableMap;

	public ChocoTranslator(Model chocoModel, Map<Variable, IntVar> variableMap) {
		this.chocoModel = chocoModel;
		this.variableMap = variableMap;
	}

	public void translate(Expression expression) throws VisitorException {
		expression.accept(this);
		assert (stack.isEmpty() || (stack.pop() == placeholder));
	}

	@Override
	public void postVisit(IntConstant constant) {
		stack.push(constant.getValue());
	}

	@Override
	public void postVisit(IntVariable variable) {
		IntVar v = variableMap.get(variable);
		if (v == null) {
			Integer lower = variable.getLowerBound();
			Integer upper = variable.getUpperBound();
			v = chocoModel.intVar(variable.getName(), lower, upper);
			variableMap.put(variable, v);
		}
		stack.push(v);
	}

	private void clause(Object left, Object right, BiFunction<Integer, Integer, Boolean> va,
			BiFunction<ArExpression, Integer, ReExpression> vj, BiFunction<ArExpression, Integer, ReExpression> vi,
			BiFunction<ArExpression, ArExpression, ReExpression> vv) {
		if ((left instanceof Integer) && (right instanceof Integer)) {
			(va.apply((Integer) left, (Integer) right) ? chocoModel.trueConstraint() : chocoModel.falseConstraint())
					.post();
		} else if ((left instanceof IntVar) && (right instanceof Integer)) {
			vi.apply((ArExpression) left, (Integer) right).post();
		} else if ((left instanceof Integer) && (right instanceof IntVar)) {
			vj.apply((ArExpression) right, (Integer) left).post();
		} else {
			vv.apply((ArExpression) left, (ArExpression) right).post();
		}
		stack.push(placeholder);
	}

	private void clause(Object left, Object right, BiFunction<Integer, Integer, Boolean> va,
			BiFunction<ArExpression, Integer, ReExpression> vi,
			BiFunction<ArExpression, ArExpression, ReExpression> vv) {
		clause(left, right, va, vi, vi, vv);
	}

	private void term(Object left, Object right, BiFunction<Integer, Integer, Integer> va,
			BiFunction<ArExpression, Integer, ArExpression> vi,
			BiFunction<ArExpression, ArExpression, ArExpression> vv) {
		if ((left instanceof Integer) && (right instanceof Integer)) {
			stack.push(va.apply((Integer) left, (Integer) right));
		} else if ((left instanceof IntVar) && (right instanceof Integer)) {
			stack.push(vi.apply((ArExpression) left, (Integer) right));
		} else if ((left instanceof Integer) && (right instanceof IntVar)) {
			stack.push(vi.apply((ArExpression) right, (Integer) left));
		} else {
			stack.push(vv.apply((ArExpression) left, (ArExpression) right));
		}
	}

	@Override
	public void postVisit(Operation operation) throws TranslatorUnsupportedOperation {
		Object l = null;
		Object r = null;
		int arity = operation.getOperator().getArity();
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
		switch (operation.getOperator()) {
		case EQ:
			clause(l, r, (a, b) -> a == b, (a, b) -> a.eq(b), (a, b) -> a.eq(b));
			break;
		case NE:
			clause(l, r, (a, b) -> a != b, (a, b) -> a.ne(b), (a, b) -> a.ne(b));
			break;
		case LT:
			clause(l, r, (a, b) -> a < b, (a, b) -> a.gt(b), (a, b) -> a.lt(b), (a, b) -> a.lt(b));
			break;
		case LE:
			clause(l, r, (a, b) -> a <= b, (a, b) -> a.ge(b), (a, b) -> a.le(b), (a, b) -> a.le(b));
			break;
		case GT:
			clause(l, r, (a, b) -> a > b, (a, b) -> a.lt(b), (a, b) -> a.gt(b), (a, b) -> a.gt(b));
			break;
		case GE:
			clause(l, r, (a, b) -> a >= b, (a, b) -> a.le(b), (a, b) -> a.ge(b), (a, b) -> a.ge(b));
			break;
		case AND:
			if (l != null) {
				assert (l == placeholder);
			}
			if (r != null) {
				assert (r == placeholder);
			}
			break;
		case ADD:
			term(l, r, (a, b) -> a + b, (a, b) -> a.add(b), (a, b) -> a.add(b));
			break;
		case SUB:
			term(l, r, (a, b) -> a - b, (a, b) -> a.sub(b), (a, b) -> a.sub(b));
			break;
		case MUL:
			term(l, r, (a, b) -> a * b, (a, b) -> a.mul(b), (a, b) -> a.mul(b));
			break;
		default:
			throw new TranslatorUnsupportedOperation("unsupported operation " + operation.getOperator());
		}
	}
}
