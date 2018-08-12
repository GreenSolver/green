package za.ac.sun.cs.green.service.simplify;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.SortedSet;
import java.util.Stack;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.logging.Level;
import java.util.stream.Stream;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.service.BasicService;
import za.ac.sun.cs.green.util.Reporter;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;

public class ConstantPropogation extends BasicService {

	/**
	 * Number of times the slicer has been invoked.
	 */
	private int invocations = 0;

	public ConstantPropogation(Green solver) {
		super(solver);
	}

	@Override
	public Set<Instance> processRequest(Instance instance) {
		@SuppressWarnings("unchecked")
		Set<Instance> result = (Set<Instance>) instance.getData(getClass());
		if (result == null) {
			final Map<Variable, Variable> map = new HashMap<Variable, Variable>();
			final Expression e = propagate(instance.getFullExpression(), map);
			final Instance i = new Instance(getSolver(), instance.getSource(), null, e);
			result = Collections.singleton(i);
			instance.setData(getClass(), result);
		}
		return result;
	}

	@Override
	public void report(Reporter reporter) {
		reporter.report(getClass().getSimpleName(), "invocations = " + invocations);
	}

	public Expression propagate(Expression expression,
			Map<Variable, Variable> map) {
		try {
			log.log(Level.FINEST, "Before Propagation: " + expression);
			invocations++;
            boolean changed = true;
            Map<IntVariable, IntConstant> constants = new HashMap<IntVariable, IntConstant>();

            int n = 0;
            while (changed) {
                OrderingVisitor orderingVisitor = new OrderingVisitor();
                ConstantVisitor constantVisitor = new ConstantVisitor(constants);
                SimplifyVisitor simplifyVisitor = new SimplifyVisitor();

                expression.accept(orderingVisitor);
                expression = orderingVisitor.getExpression();
                expression.accept(constantVisitor);
                expression = constantVisitor.getExpression();
                expression.accept(simplifyVisitor);
                expression = simplifyVisitor.getExpression();
                changed = orderingVisitor.hasChanged() || 
                    constantVisitor.hasChanged() ||
                    simplifyVisitor.hasChanged();

                if (n++ > 10) {
                    log.log(Level.FINEST, "still changed after 10 iterations: " + expression);
                    break;
                }

            }

			log.log(Level.FINEST, "After Propagation: " + expression);
			return expression;
		} catch (VisitorException x) {
			log.log(Level.SEVERE,
					"encountered an exception -- this should not be happening!",
					x);
		}
		return null;
	}

	private static class OrderingVisitor extends Visitor {

		private Stack<Expression> stack;
        private boolean changed;

		public OrderingVisitor() {
			stack = new Stack<Expression>();
            changed = false;
		}

		public boolean hasChanged() {
			return changed;
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
			stack.push(variable);
		}

		@Override
		public void postVisit(Operation operation) throws VisitorException {
			Operation.Operator op = operation.getOperator();

			switch (op) {
                case ADD:
                case MUL:
                    Expression r = stack.pop();
                    Expression l = stack.pop();

                    if (l instanceof IntConstant && r instanceof IntVariable) {
                        stack.push(new Operation(op, l, r));
                        changed = true;
                    } else {
                        stack.push(operation);
                    }

                    break;
                default:
                    for (int i = op.getArity(); i > 0; i--) {
                        stack.pop();
                    }

                    stack.push(operation);
            }
		}

	}


	private static class ConstantVisitor extends Visitor {

		private Stack<Expression> stack;
        private Map<IntVariable, IntConstant> constants;
        private boolean replace;
        private boolean changed;
        private boolean unsatisfiable;

		public ConstantVisitor(Map<IntVariable, IntConstant> constants) {
			stack = new Stack<Expression>();
            this.constants = constants;
            replace = true;
            changed = false;
            unsatisfiable = false;
		}

		public boolean hasChanged() {
			return changed;
		}

		public Expression getExpression() {
            if (unsatisfiable) {
                return Operation.FALSE;
            } else {
                return stack.pop();
            }
		}

		@Override
		public void preVisit(Operation operation) throws VisitorException {
            if (unsatisfiable) {
                return;
            }

            Operation.Operator op = operation.getOperator();

            if (op == Operation.Operator.EQ) {
                Expression r = operation.getOperand(0);
                Expression l = operation.getOperand(1);

                if (r instanceof IntVariable &&
                        l instanceof IntConstant) {
                    IntVariable v = (IntVariable) r;
                    IntConstant c = (IntConstant) l;

                    if (!constants.containsKey(v)) {
                        constants.put(v, c);
                        changed = true;
                    } else if (!constants.get(v).equals(c)) {
                        System.out.println(v + " == " + constants.get(v) + " != " + c);
                        unsatisfiable = true;
                    }

                    replace = false;
                } else if (r instanceof IntConstant &&
                        l instanceof IntVariable) {
                    IntVariable v = (IntVariable) l;
                    IntConstant c = (IntConstant) r;

                    if (!constants.containsKey(v)) {
                        constants.put(v, c);
                        changed = true;
                    } else if (!constants.get(v).equals(c)) {
                        System.out.println(v + " == " + constants.get(v) + " != " + c);
                        unsatisfiable = true;
                    }

                    replace = false;
                }
            }
        }

		@Override
		public void postVisit(IntConstant constant) {
            if (unsatisfiable) {
                return;
            }

			stack.push(constant);
		}

		@Override
		public void postVisit(IntVariable variable) {
            if (unsatisfiable) {
                return;
            }

            if (replace && constants.containsKey(variable)) {
                stack.push(constants.get(variable));
                changed = true;
            } else {
                stack.push(variable);
            }
		}

		@Override
		public void postVisit(Operation operation) throws VisitorException {
            if (unsatisfiable) {
                return;
            }

            replace = true;
			int arity = operation.getOperator().getArity();
			Expression operands[] = new Expression[arity];
			for (int i = arity; i > 0; i--) {
				operands[i - 1] = stack.pop();
			}
			stack.push(new Operation(operation.getOperator(), operands));
		}
	}

	private static class SimplifyVisitor extends Visitor {

		private Stack<Expression> stack;
        private boolean changed;

		public SimplifyVisitor() {
			stack = new Stack<Expression>();
            changed = false;
		}

		public Expression getExpression() {
			return stack.pop();
		}

		public boolean hasChanged() {
			return changed;
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
			int arity = operation.getOperator().getArity();
			Expression operands[] = new Expression[arity];
			for (int i = arity; i > 0; i--) {
				operands[i - 1] = stack.pop();
			}

            Stream<Expression> str = Arrays.stream(operands);
            
            if (str.allMatch(e -> 
                        e instanceof IntConstant 
                        || e.equals(Operation.TRUE) 
                        || e.equals(Operation.FALSE)
                    )) {
                simplifyConstants(operation, operands);
            } else {
                simplifyRelations(operation, operands);
            }

		}

        private void simplifyRelations(Operation operation, Expression[] operands) {
            Operation.Operator op = operation.getOperator();

            switch (op) {
                case EQ:
                case NE:
                case LT:
                case GT:
                case LE:
                case GE:
                    Expression l = operands[0];
                    Expression r = operands[1];
                    Operation.Operator op2 = null;
                    Operation operator = null;
                    IntConstant constant = null;
                    boolean eq = false;
                    boolean lefty = false;

                    if (l instanceof Operation && r instanceof IntConstant) {
                        op2 = ((Operation) l).getOperator();
                        operator = (Operation) l;
                        constant = (IntConstant) r;
                        eq = true;
                        lefty = true;
                    } else if (r instanceof Operation && l instanceof IntConstant) {
                        op2 = ((Operation) r).getOperator();
                        operator = (Operation) r;
                        constant = (IntConstant) l;
                        eq = true;
                    }

                    if (eq) {
                        Operation.Operator nop = null;

                        switch (op2) {
                            case ADD:
                                nop = Operation.Operator.SUB;
                                break;
                            case SUB:
                                nop = Operation.Operator.ADD;
                                break;
                        }

                        if (nop != null) {
                            changed = true;
                            Expression left, right;

                            if (lefty) {
                                left = operator.getOperand(0);
                                right = new Operation(nop, constant, operator.getOperand(1));
                            } else {
                                left = new Operation(nop, constant, operator.getOperand(1));
                                right = operator.getOperand(0);
                            }

                            operands[0] = left;
                            operands[1] = right;
                        }
                    }

                    break;

                case AND:
                    l = operands[0];
                    r = operands[1];

                    if (l.equals(Operation.TRUE)) {
                        stack.push(r);
                    } else if (r.equals(Operation.TRUE)) {
                        stack.push(l);
                    } else if (l.equals(Operation.FALSE)) {
                        stack.push(l);
                    } else if (r.equals(Operation.FALSE)) {
                        stack.push(r);
                    } else {
                        break;
                    }

                    System.out.println("Simplified AND to " + stack.peak());

                    return;

                case OR:
                    l = operands[0];
                    r = operands[1];

                    if (l.equals(Operation.TRUE)) {
                        stack.push(l);
                    } else if (r.equals(Operation.TRUE)) {
                        stack.push(r);
                    } else if (l.equals(Operation.FALSE)) {
                        stack.push(r);
                    } else if (r.equals(Operation.FALSE)) {
                        stack.push(l);
                    } else {
                        break;
                    }

                    System.out.println("Simplified OR");
                    return;
            }

            stack.push(new Operation(operation.getOperator(), operands));
        }

        private void simplifyConstants(Operation operation, Expression[] operands) {
            Stream<Expression> str = Arrays.stream(operands);
            Operation.Operator op = operation.getOperator();

            switch (op) {
                case EQ:
                    if (operation.equals(Operation.TRUE) || operation.equals(Operation.FALSE)) {
                        stack.push(operation);
                        return;
                    }
                    stack.push(operands[0].equals(operands[1]) ?
                            Operation.TRUE : Operation.FALSE);
                    break;
                case NE:
                    stack.push(!operands[0].equals(operands[1]) ?
                            Operation.TRUE : Operation.FALSE);
                    break;
                case LT:
                    stack.push(((IntConstant) operands[0]).getValue() <
                            ((IntConstant) operands[1]).getValue() ?
                            Operation.TRUE : Operation.FALSE);
                    break;
                case GT:
                    stack.push(((IntConstant) operands[0]).getValue() >
                            ((IntConstant) operands[1]).getValue() ?
                            Operation.TRUE : Operation.FALSE);
                    break;
                case LE:
                    stack.push(((IntConstant) operands[0]).getValue() <=
                            ((IntConstant) operands[1]).getValue() ?
                            Operation.TRUE : Operation.FALSE);
                    break;
                case GE:
                    stack.push(((IntConstant) operands[0]).getValue() >=
                            ((IntConstant) operands[1]).getValue() ?
                            Operation.TRUE : Operation.FALSE);
                    break;

                case AND:
                    stack.push(str.allMatch(e -> e.equals(Operation.TRUE)) ?
                                Operation.TRUE : Operation.FALSE);
                    break;
                case OR:
                    stack.push(str.anyMatch(e -> e.equals(Operation.TRUE)) ?
                                Operation.TRUE : Operation.FALSE);
                    break;

                case ADD:
                    stack.push(new IntConstant(str
                                .mapToInt(e -> ((IntConstant) e).getValue())
                                .sum()));
                    break;
                case SUB:
                    stack.push(new IntConstant(((IntConstant) operands[0]).getValue() -
                            ((IntConstant) operands[1]).getValue()));
                    break;
                case MUL:
                    stack.push(new IntConstant(((IntConstant) operands[0]).getValue() *
                            ((IntConstant) operands[1]).getValue()));
                    break;
                case DIV:
                    stack.push(new IntConstant(((IntConstant) operands[0]).getValue() /
                            ((IntConstant) operands[1]).getValue()));
                    break;
                case MOD:
                    stack.push(new IntConstant(((IntConstant) operands[0]).getValue() %
                            ((IntConstant) operands[1]).getValue()));
                    break;
                case NEG:
                    stack.push(new IntConstant(-((IntConstant) operands[0]).getValue()));
                    break;

                default:
                    stack.push(operation);
                    return;
            }

            changed = true;
        }

	}

}
