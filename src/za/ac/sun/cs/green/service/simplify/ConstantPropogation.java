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
            //boolean result = true;
            Map<IntVariable, IntConstant> constants = new HashMap<IntVariable, IntConstant>();

            //while (result) {
            ConstantVisitor constantVisitor = new ConstantVisitor(constants);
            expression.accept(constantVisitor);
            expression = constantVisitor.getExpression();
            SimplifyVisitor simplifyVisitor = new SimplifyVisitor();
            expression.accept(simplifyVisitor);
            expression = simplifyVisitor.getExpression();
            //}

			log.log(Level.FINEST, "After Propagation: " + expression);
			return expression;
		} catch (VisitorException x) {
			log.log(Level.SEVERE,
					"encountered an exception -- this should not be happening!",
					x);
		}
		return null;
	}

	private static class ConstantVisitor extends Visitor {

		private Stack<Expression> stack;
        private Map<IntVariable, IntConstant> constants;
        private boolean replace = true;

		public ConstantVisitor(Map<IntVariable, IntConstant> constants) {
			stack = new Stack<Expression>();
            this.constants = constants;
		}

		public Expression getExpression() {
			return stack.pop();
		}

		@Override
		public void preVisit(Operation operation) throws VisitorException {
            Operation.Operator op = operation.getOperator();

            if (op == Operation.Operator.EQ) {
                Expression r = operation.getOperand(0);
                Expression l = operation.getOperand(1);

                if (r instanceof IntVariable &&
                        l instanceof IntConstant) {
                    constants.put((IntVariable) r, (IntConstant) l);
                    replace = false;
                } else if (r instanceof IntConstant &&
                        l instanceof IntVariable) {
                    constants.put((IntVariable) l, (IntConstant) r);
                    replace = false;
                }
            }
        }

		@Override
		public void postVisit(IntConstant constant) {
			stack.push(constant);
		}

		@Override
		public void postVisit(IntVariable variable) {
            if (replace && constants.containsKey(variable)) {
                stack.push(constants.get(variable));
            } else {
                stack.push(variable);
            }
		}

		@Override
		public void postVisit(Operation operation) throws VisitorException {
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

		public SimplifyVisitor() {
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
                    // TODO
                    break;
                default:
                    stack.push(new Operation(operation.getOperator(), operands));
            }
        }

        private void simplifyConstants(Operation operation, Expression[] operands) {
            Stream<Expression> str = Arrays.stream(operands);
            Operation.Operator op = operation.getOperator();

            switch (op) {
                case EQ:
                    stack.push(operands[0].equals(operands[1]) ?
                            Operation.TRUE : Operation.FALSE);
                    break;
                case NE:
                    stack.push(!operands[0].equals(operands[1]) ?
                            Operation.TRUE : Operation.FALSE);
                    break;
                case LT:
                    stack.push(operands[0].compareTo(operands[1]) < 0 ?
                            Operation.TRUE : Operation.FALSE);
                    break;
                case GT:
                    stack.push(operands[0].compareTo(operands[1]) > 0 ?
                            Operation.TRUE : Operation.FALSE);
                    break;
                case LE:
                    stack.push(operands[0].compareTo(operands[1]) <= 0 ?
                            Operation.TRUE : Operation.FALSE);
                    break;
                case GE:
                    stack.push(operands[0].compareTo(operands[1]) >= 0 ?
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
            }
        }

	}

}
