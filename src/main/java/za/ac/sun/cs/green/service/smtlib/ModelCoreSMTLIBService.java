package za.ac.sun.cs.green.service.smtlib;
import java.util.*;

import org.apache.logging.log4j.Level;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.*;
import za.ac.sun.cs.green.expr.Operation.Operator;
import za.ac.sun.cs.green.service.ModelCoreService;
import za.ac.sun.cs.green.util.Misc;

public abstract class ModelCoreSMTLIBService extends ModelCoreService {

	public ModelCoreSMTLIBService(Green solver) {
		super(solver);
	}

	@Override
	public ModelCore modelCore(Instance instance) {
		try {
			Translator t = new Translator();
			instance.getExpression().accept(t);
			StringBuilder b = new StringBuilder();
			b.append("(set-option :produce-models true)");
			b.append("(set-option :produce-unsat-cores true)");
			b.append("(set-option :auto-config false)"); // get a smaller core
//            b.append("(set-option :relevancy 0)"); // get a smaller core
//            b.append("(set-option :solver false)"); // get a smaller core
			b.append("(set-logic QF_LIA)"); // AUFLIRA ???
			b.append(Misc.join(t.getVariableDecls(), " "));
			b.append(Misc.join(t.getClauseDecls(), " "));
			b.append(Misc.join(t.getAsserts(), " "));
			b.append("(check-sat)");
			return solve0(b.toString(), t.getVariables(), t.getCoreClauseMapping());
		} catch (TranslatorUnsupportedOperation x) {
			log.log(Level.WARN, x.getMessage(), x);
		} catch (VisitorException x) {
			log.log(Level.FATAL, x.getMessage(), x);
		}
		return null;
	}

	protected abstract ModelCore solve0(String smtQuery, Map<Variable, String> variables, Map<String, Expression> coreClauseMapping);

	@SuppressWarnings("serial")
	private static class TranslatorUnsupportedOperation extends
			VisitorException {

		public TranslatorUnsupportedOperation(String message) {
			super(message);
		}

	}

	private static class TranslatorPair {
		private final String string;
		private final Class<? extends Variable> type;
		public TranslatorPair(final String string, final Class<? extends Variable> type) {
			this.string = string;
			this.type = type;
		}
		public String getString() {
			return string;
		}
		public Class<? extends Variable> getType() {
			return type;
		}
	}

	private static class Translator extends Visitor {

		private final Stack<TranslatorPair> stack;
		private final String PREFIX = "x";
		private final List<String> domains;
		private final List<String> asserts;
		private final List<String> defs;
		private Map<String, Expression> coreClauseMapping;
		private Map<Variable, String> varMap;
		private int counter = 0;
		private int ordepth = 0;

		public Translator() {
			stack = new Stack<TranslatorPair>();
			varMap = new HashMap<Variable, String>();
			defs = new LinkedList<String>();
			domains = new LinkedList<String>();
			asserts = new LinkedList<String>();
			coreClauseMapping = new HashMap<String, Expression>();
		}

        public Map<Variable, String> getVariables() {
            return varMap;
        }

        public List<String> getVariableDecls() {
            return defs;
        }

        public List<String> getClauseDecls() {
			return domains;
		}

		public List<String> getAsserts() { return asserts; }

		public Map<String, Expression> getCoreClauseMapping() {
			return coreClauseMapping;
		}

		private String buildAssert(String name) {
		    return new StringBuilder().append("(assert (! ").append(name).append(" :named ").append(PREFIX).append(name).append("))").toString();
		}

		public String getTranslation() {
			StringBuilder b = new StringBuilder();
			b.append("(and");
			for (String domain : domains) {
				b.append(' ').append(domain);
			}
			TranslatorPair p = stack.pop();
			b.append(' ').append(p.getString()).append(')');
			assert stack.isEmpty();
			return b.toString();
		}

		private String transformNegative(int v) {
			if (v < 0) {
				StringBuilder b = new StringBuilder();
				b.append("(- ").append(-v).append(')');
				return b.toString();
			} else {
				return Integer.toString(v);
			}
		}

		@Override
		public void postVisit(IntConstant constant) {
			int val = constant.getValue();
			stack.push(new TranslatorPair(transformNegative(val), IntVariable.class));
		}

		@Override
		public void postVisit(IntVariable variable) {
			String v = varMap.get(variable);
			String n = variable.getName();
			if (v == null) {
				StringBuilder b = new StringBuilder();
				StringBuilder bn = new StringBuilder();
				b.append("(declare-const ").append(n).append(" Int)");
				defs.add(b.toString());
				// lower bound
                b.setLength(0);
                bn.setLength(0);
                b.append("(>= ").append(n).append(' ').append(transformNegative(variable.getLowerBound())).append(')');
                String lbound = b.toString();
                Expression lboundExpr = new Operation(Operator.GE, variable, new IntConstant(variable.getLowerBound()));
				b.setLength(0);
				bn.append(n).append("-lower");
				b.append("(define-const ").append(bn);
				b.append(" Bool ").append(lbound).append(')');
				coreClauseMapping.put(PREFIX + bn, lboundExpr);
				asserts.add(buildAssert(bn.toString()));
				domains.add(b.toString());
				// upper bound
                b.setLength(0);
                bn.setLength(0);
                b.append("(<= ").append(n).append(' ').append(transformNegative(variable.getUpperBound())).append(')');
                String ubound = b.toString();
                Expression uboundExpr = new Operation(Operator.LE, variable, new IntConstant(variable.getUpperBound()));
                b.setLength(0);
                bn.append(n).append("-upper");
                b.append("(define-const ").append(bn);
                b.append(" Bool ").append(ubound).append(')');
                coreClauseMapping.put(PREFIX + bn, uboundExpr);
				asserts.add(buildAssert(bn.toString()));
				domains.add(b.toString());
				varMap.put(variable, n);
			}
			stack.push(new TranslatorPair(n, IntVariable.class));
		}

		private Class<? extends Variable> superType(TranslatorPair left, TranslatorPair right) {
			if ((left.getType() == RealVariable.class) || (right.getType() == RealVariable.class)) {
				return RealVariable.class;
			} else {
				return IntVariable.class;
			}
		}

		private String adjust(TranslatorPair term, Class<? extends Variable> type) {
			String s = term.getString();
			Class<? extends Variable> t = term.getType();
			if (t == type) {
				return s;
			} else {
				StringBuilder b = new StringBuilder();
				b.append("(to_real ").append(s).append(')');
				return b.toString();
			}
		}

		private String setOperator(Operator op) throws TranslatorUnsupportedOperation {
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
				case BIT_AND:
				case BIT_OR:
				case BIT_XOR:
				case SHIFTL:
				case SHIFTR:
				case SHIFTUR:
				case SIN:
				case COS:
				case TAN:
				case ASIN:
				case ACOS:
				case ATAN:
				case ATAN2:
				case ROUND:
				case LOG:
				case EXP:
				case POWER:
				case SQRT:
				default:
					throw new TranslatorUnsupportedOperation(
							"unsupported operation " + op);
			}
		}

		public void preVisit(Operation operation) throws TranslatorUnsupportedOperation {
			if (operation.getOperator() == Operator.OR) {
				ordepth++;
			}
		}
		
		public void postVisit(Operation operation) throws TranslatorUnsupportedOperation {
			TranslatorPair l = null;
			TranslatorPair r = null;
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

			if (op == Operator.OR) {
				ordepth--;
			}
			switch (op) {
				case EQ:
				case NE:
				case LT:
				case LE:
				case GT:
				case GE:
				case AND:
				case OR:
					StringBuilder bb = new StringBuilder();
					bb.setLength(0);
					String bn = "q" + counter++;
					bb.append("(define-const ").append(bn);
					bb.append(" Bool ").append(b.toString());
					bb.append(')');
					coreClauseMapping.put(PREFIX + bn, operation);
					if (ordepth == 0) {
						asserts.add(buildAssert(bn));
					}
					domains.add(bb.toString());
					break;
				default:
					break;
			}
			stack.push(new TranslatorPair(b.toString(), v));
		}
	}

}
