package za.ac.sun.cs.green.service.simplifier;

import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.service.BasicService;
import za.ac.sun.cs.green.util.Reporter;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;

public class SATPropagationService extends BasicService {

	/**
	 * Number of times the simplifier has been invoked.
	 */
	private int invocations = 0;
	private int simplifications = 0;
	private int propagations = 0;
	private long timeConsumption = 0;

	public SATPropagationService(Green solver) {
		super(solver);
	}

	@Override
	public Set<Instance> processRequest(Instance instance) {
		long start = System.currentTimeMillis();
		@SuppressWarnings("unchecked")
		Set<Instance> result = (Set<Instance>) instance.getData(getClass());
		if (result == null) {
			final Map<Variable, Variable> map = new HashMap<Variable, Variable>();
			final Expression e = simplify(instance.getFullExpression(), map);
			final Instance i = new Instance(getSolver(), instance.getSource(), null, e);
			result = Collections.singleton(i);
			instance.setData(getClass(), result);
		}
		timeConsumption += (System.currentTimeMillis() - start);
		return result;
	}

	@Override
	public void report(Reporter reporter) {
		reporter.report(getClass().getSimpleName(), "invocations = " + invocations);
		reporter.report(getClass().getSimpleName(), "simplifications = " + simplifications);
		reporter.report(getClass().getSimpleName(), "propagations = " + propagations);
		reporter.report(getClass().getSimpleName(), "timeConsumption = " + timeConsumption);
	}

	public Expression simplify(Expression expression) {
		List<Tuple> totalConstants = new LinkedList<>();
		boolean done = false;
		try {
			while (!done) {
				CollectionVisitor colVisitor = new CollectionVisitor();
				expression.accept(colVisitor);
				simplifications += colVisitor.getSimplifications();
				List<Tuple> vars = colVisitor.getVars();
//                for (Tuple v : vars) {
//                    System.out.print(v.getVariable() + "=" + v.getValue() + ", ");
//                }
//                System.out.println();
				if (vars.isEmpty()) {
					done = true;
				} else {
					totalConstants.addAll(vars);
					ReplaceVisitor repVisitor = new ReplaceVisitor(vars);
					expression.accept(repVisitor);
					expression = repVisitor.getExpression();
					simplifications += repVisitor.getSimplifications();
					propagations += repVisitor.getPropagations(); // correct???
				}
			}
			// remember conjuncts, to prevent duplicates in answer
			HashMap<Expression, Integer> conjuncts = new HashMap<>();
			for (Tuple t : totalConstants) {
				Expression eq = new Operation(Operation.Operator.EQ, t.getVariable(), t.getValue());
				if (expression.equals(Operation.TRUE)) {
					expression = eq;
				} else {
					if (conjuncts.get(eq) == null) {
						conjuncts.put(eq, 1);
						expression = new Operation(Operation.Operator.AND, expression, eq);
					}
				}
			}
			return expression;
		} catch (VisitorException x) {
			log.fatal("encountered an exception -- this should not be happening!", x);
		}
		return null;
	}

	public Expression simplify(Expression expression, Map<Variable, Variable> map) {
		invocations++;
		return simplify(expression);
	}

	private static class Tuple {
		IntVariable var;
		Expression value;

		Tuple(IntVariable v, Expression c) {
			var = v;
			value = c;
		}

		public IntVariable getVariable() {
			return var;
		}

		public Expression getValue() {
			return value;
		}
	}

	private static class CollectionVisitor extends Visitor {

		private List<Tuple> varsList;
		private Stack<Object> stack;
		private int simplifications = 0;

		CollectionVisitor() {
			varsList = new LinkedList<>();
			stack = new Stack<>();
		}

		public List<Tuple> getVars() {
			return varsList;
		}

		@Override
		public void postVisit(IntConstant constant) {
			stack.push(constant);
		}

		@Override
		public void postVisit(IntVariable variable) {
			stack.push(variable);
		}

		@Override
		public void postVisit(Operation operation) throws VisitorException {
			Object l = null;
			Object r = null;

			Operation.Operator op = operation.getOperator();
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

			if (l == null) {
				return;
			}

			switch (op) {
			case LE:
				stack.push(l);
				stack.push(r);
				break;
			case LT:
				stack.push(l);
				stack.push(r);
				break;
			case AND:
				stack.push(l);
				stack.push(r);
				break;
			case ADD:
				if ((l instanceof IntConstant) && (r instanceof IntConstant)) {
					simplifications++;
					stack.push(new IntConstant(((IntConstant) l).getValue() + ((IntConstant) r).getValue()));
				} else {
					stack.push(new Operation(Operation.Operator.ADD, (Expression) l, (Expression) r));
				}
				break;
			case SUB:
				if ((l instanceof IntConstant) && (r instanceof IntConstant)) {
					simplifications++;
					stack.push(new IntConstant(((IntConstant) l).getValue() - ((IntConstant) r).getValue()));
				} else {
					stack.push(new Operation(Operation.Operator.SUB, (Expression) l, (Expression) r));
				}
				break;
			case EQ:
				if (l instanceof IntVariable) {
					if (r instanceof IntConstant) {
						Tuple tup = new Tuple((IntVariable) l, (IntConstant) r);
						varsList.add(tup);
					} else if (r instanceof IntVariable) {
						Tuple tup = new Tuple((IntVariable) l, (IntVariable) r);
						varsList.add(tup);
					} else {
						stack.push(l);
						stack.push(r);
					}
				} else {
					stack.push(l);
					stack.push(r);
				}
				break;
			case GE:
				stack.push(l);
				stack.push(r);
				break;
			case GT:
				stack.push(l);
				stack.push(r);
				break;
			case MUL:
				if ((l instanceof IntConstant) && (r instanceof IntConstant)) {
					simplifications++;
					stack.push(new IntConstant(((IntConstant) l).getValue() * ((IntConstant) r).getValue()));
				} else if ((l instanceof IntConstant) && (r instanceof IntVariable)) {
					simplifyMulOp((IntConstant) l, (IntVariable) r, stack);
				} else if ((l instanceof IntVariable) && (r instanceof IntConstant)) {
					simplifyMulOp((IntConstant) r, (IntVariable) l, stack);
				} else {
					stack.push(new Operation(Operation.Operator.MUL, (Expression) l, (Expression) r));
				}
				break;
			case OR:
				stack.push(l);
				stack.push(r);
				break;
			case NE:
				stack.push(l);
				stack.push(r);
				break;
			default:
				break;
			}
		}

		private void simplifyMulOp(IntConstant a, IntVariable b, Stack<Object> stack) {
			if (a.getValue() == 0) {
				simplifications++;
				stack.push(new IntConstant(0));
			} else if (a.getValue() == 1) {
				simplifications++;
				stack.push(b);
			} else {
				stack.push(new Operation(Operation.Operator.MUL, a, b));
			}
		}

		public int getSimplifications() {
			return simplifications;
		}
	}

	private static class ReplaceVisitor extends Visitor {

		private Map<IntVariable, Expression> map;
		private Stack<Expression> stack;
		private int propagations = 0;
		private int simplifications = 0;
		// private List<Tuple> eqConstraints;

		ReplaceVisitor(List<Tuple> vars) {
			// eqConstraints = vars;
			map = new HashMap<>();
			for (Object t : vars) {
				map.put(((Tuple) t).getVariable(), ((Tuple) t).getValue());
			}
			stack = new Stack<Expression>();
		}

		public Expression getExpression() {
			return stack.pop();
		}

		@Override
		public void postVisit(IntConstant constant) {
			stack.push(constant);
		}

		@Override
		public void postVisit(IntVariable variable) {
			Expression c = map.get(variable);
			if (c == null) {
				stack.push(variable);
			} else {
				propagations++;
				stack.push(c);
			}
		}

		private Expression applyOperation(Operation.Operator op, IntConstant l, IntConstant r) {
			simplifications++;
			switch (op) {
			case ADD:
				return new IntConstant(l.getValue() + r.getValue());
			case SUB:
				return new IntConstant(l.getValue() - r.getValue());
			case DIV:
				return new IntConstant(l.getValue() / r.getValue());
			case MUL:
				return new IntConstant(l.getValue() * r.getValue());
			case LE:
				return (l.getValue() <= r.getValue()) ? Operation.TRUE : Operation.FALSE;
			case LT:
				return (l.getValue() < r.getValue()) ? Operation.TRUE : Operation.FALSE;
			case GE:
				return (l.getValue() >= r.getValue()) ? Operation.TRUE : Operation.FALSE;
			case GT:
				return (l.getValue() > r.getValue()) ? Operation.TRUE : Operation.FALSE;
			default:
				return new Operation(op, l, r);
			}
		}

		private Expression applyOperation(Operation.Operator op, IntVariable l, IntVariable r) {
			switch (op) {
			case EQ:
				return (l.equals(r)) ? Operation.TRUE : new Operation(op, l, r);
			default:
				return new Operation(op, l, r);
			}
		}

		@Override
		public void postVisit(Operation operation) throws VisitorException {
			Operation.Operator op = operation.getOperator();
			if (op.getArity() == 2) {
				Expression r = stack.pop();
				Expression l = stack.pop();
				if ((op == Operation.Operator.EQ) && (l instanceof IntConstant) && (r instanceof IntConstant)) {
					IntConstant left = (IntConstant) l;
					IntConstant right = (IntConstant) r;
					stack.push(left.equals(right) ? Operation.TRUE : Operation.FALSE);
				} else if (l instanceof IntVariable && r instanceof IntVariable) {
					stack.push(applyOperation(op, (IntVariable) l, (IntVariable) r));
				} else if (l instanceof IntConstant && r instanceof IntConstant) {
					stack.push(applyOperation(op, (IntConstant) l, (IntConstant) r));
				} else if (l instanceof IntConstant) {
					stack.push(new Operation(op, ((IntConstant) l), r));
				} else if (r instanceof IntConstant) {
					stack.push(new Operation(op, l, (IntConstant) r));
				} else {
					if (l.equals(Operation.TRUE) && r.equals(Operation.TRUE)) {
						stack.push(Operation.TRUE);
					} else if (l.equals(Operation.FALSE) || r.equals(Operation.FALSE)) {
						stack.push(Operation.FALSE);
					} else if (l.equals(Operation.TRUE)) {
						stack.push(r);
					} else if (r.equals(Operation.TRUE)) {
						stack.push(l);
					} else {
						stack.push(new Operation(op, l, r));
					}
				}
			} else {
				for (int i = op.getArity(); i > 0; i--) {
					stack.pop();
				}
				stack.push(operation);
			}
		}

		public int getPropagations() {
			return propagations;
		}

		public int getSimplifications() {
			return simplifications;
		}
	}

}
