package za.ac.sun.cs.green.service.choco4;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.expression.discrete.arithmetic.ArExpression;
import org.chocosolver.solver.expression.discrete.relational.ReExpression;
import org.chocosolver.solver.variables.IntVar;

public class ChocoTranslator extends Visitor {

	private Model chocoModel = null;

	private Stack<Object> stack = null;

	private List<ReExpression> constraints = null;

	private Map<Variable, IntVar> variableMap = null;

	public ChocoTranslator(Model chocoModel, Map<Variable, IntVar> variableMap) {
		this.chocoModel = chocoModel;
		stack = new Stack<Object>();
		constraints = new LinkedList<ReExpression>();
		this.variableMap = variableMap;
	}

	public void translate(Expression expression) throws VisitorException {
		expression.accept(this);
		for (ReExpression c : constraints) {
			c.post();
		}
		if (!stack.isEmpty()) {
			((ReExpression) stack.pop()).post();
		}
		assert stack.isEmpty();
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
			if (l instanceof Integer) {
				stack.push(((ArExpression) r).eq((Integer) l));
			} else if (r instanceof Integer) {
				stack.push(((ArExpression) l).eq((Integer) r));
			} else {
				stack.push(((ArExpression) l).eq((ArExpression) r));
			}
			break;
		case NE:
			if (l instanceof Integer) {
				stack.push(((ArExpression) r).ne((Integer) l));
			} else if (r instanceof Integer) {
				stack.push(((ArExpression) l).ne((Integer) r));
			} else {
				stack.push(((ArExpression) l).ne((ArExpression) r));
			}
			break;
		case LT:
			if (l instanceof Integer) {
				stack.push(((ArExpression) r).gt((Integer) l));
			} else if (r instanceof Integer) {
				stack.push(((ArExpression) l).lt((Integer) r));
			} else {
				stack.push(((ArExpression) l).lt((ArExpression) r));
			}
			break;
		case LE:
			if (l instanceof Integer) {
				stack.push(((ArExpression) r).ge((Integer) l));
			} else if (r instanceof Integer) {
				stack.push(((ArExpression) l).le((Integer) r));
			} else {
				stack.push(((ArExpression) l).le((ArExpression) r));
			}
			break;
		case GT:
			if (l instanceof Integer) {
				stack.push(((ArExpression) r).lt((Integer) l));
			} else if (r instanceof Integer) {
				stack.push(((ArExpression) l).gt((Integer) r));
			} else {
				stack.push(((ArExpression) l).gt((ArExpression) r));
			}
			break;
		case GE:
			if (l instanceof Integer) {
				stack.push(((ArExpression) r).le((Integer) l));
			} else if (r instanceof Integer) {
				stack.push(((ArExpression) l).ge((Integer) r));
			} else {
				stack.push(((ArExpression) l).ge((ArExpression) r));
			}
			break;
		case AND:
			if (l != null) {
				constraints.add((ReExpression) l);
			}
			if (r != null) {
				constraints.add((ReExpression) r);
			}
			break;
		case ADD:
			if (l instanceof Integer) {
				stack.push(((ArExpression) r).add((Integer) l));
			} else if (r instanceof Integer) {
				stack.push(((ArExpression) l).add((Integer) r));
			} else {
				stack.push(((ArExpression) l).add((ArExpression) r));
			}
			break;
		case SUB:
			if (l instanceof Integer) {
				stack.push(((ArExpression) r).sub((Integer) l).neg());
			} else if (r instanceof Integer) {
				stack.push(((ArExpression) l).sub((Integer) r));
			} else {
				stack.push(((ArExpression) l).sub((ArExpression) r));
			}
			break;
		case MUL:
			if (l instanceof Integer) {
				stack.push(((ArExpression) r).mul((Integer) l));
			} else if (r instanceof Integer) {
				stack.push(((ArExpression) l).mul((Integer) r));
			} else {
				stack.push(((ArExpression) l).mul((ArExpression) r));
			}
			break;
		default:
			throw new TranslatorUnsupportedOperation("unsupported operation " + operation.getOperator());
		}
	}
}
