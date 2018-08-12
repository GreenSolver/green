package za.ac.sun.cs.green.service.simplify;

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
            //SimplifyVisitor simplifyVisitor = new SimplifyVisitor();
            expression.accept(constantVisitor);
            expression = constantVisitor.getExpression();
            //expression.accept(simplifyVisitor);
            //Expression canonized = simplifyVisitor.getExpression();
            //}

            //Expression canonized = simplifyVisitor.getExpression();

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
	}

	private static class Renamer extends Visitor {

		private Map<Variable, Variable> map;

		private Stack<Expression> stack;

		public Renamer(Map<Variable, Variable> map,
				SortedSet<IntVariable> variableSet) {
			this.map = map;
			stack = new Stack<Expression>();
		}

		public Expression rename(Expression expression) throws VisitorException {
			expression.accept(this);
			return stack.pop();
		}

		@Override
		public void postVisit(IntVariable variable) {
			Variable v = map.get(variable);
			if (v == null) {
				v = new IntVariable("v" + map.size(), variable.getLowerBound(),
						variable.getUpperBound());
				map.put(variable, v);
			}
			stack.push(v);
		}

		@Override
		public void postVisit(IntConstant constant) {
			stack.push(constant);
		}

		@Override
		public void postVisit(Operation operation) {
			int arity = operation.getOperator().getArity();
			Expression operands[] = new Expression[arity];
			for (int i = arity; i > 0; i--) {
				operands[i - 1] = stack.pop();
			}
			stack.push(new Operation(operation.getOperator(), operands));
		}

	}

}
