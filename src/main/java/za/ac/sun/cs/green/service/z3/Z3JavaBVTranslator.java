package za.ac.sun.cs.green.service.z3;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FPExpr;
import com.microsoft.z3.Z3Exception;

import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.RealConstant;
import za.ac.sun.cs.green.expr.RealVariable;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;

public class Z3JavaBVTranslator extends Visitor {

	private Context context = null;
	private Stack<Expr> stack = null;
	private List<BoolExpr> domains = null;
	private Map<Expression, Expr> asserts = null; // maps the Green expressions to Context expressions
	private Map<BoolExpr, Expression> coreClauseMapping; // maps the Context names to Green expressions
	private Map<Variable, Expr> v2e = null; // maps Green variables to Context format
	private int counter = 0; // counter for the predicate names
	private int size = Integer.SIZE; // Default Bitvector size

	public Z3JavaBVTranslator(Context c) {
		this.context = c;
		stack = new Stack<Expr>();
		v2e = new HashMap<Variable, Expr>();
		domains = new LinkedList<BoolExpr>();
		asserts = new HashMap<>();
		coreClauseMapping = new HashMap<>();
	}

	public BoolExpr getTranslation() {
		BoolExpr result = (BoolExpr) stack.pop();
		/* not required due to Bounder being used */
		/*
		 * not sure why this was commented out, it is clearly wrong, with or without
		 * bounder
		 */
		for (BoolExpr expr : domains) {
			try {
				result = context.mkAnd(result, expr);
			} catch (Z3Exception e) {
				e.printStackTrace();
			}
		}
		/* was end of old comment */
		return result;
	}

	public Map<BoolExpr, Expression> getCoreMappings() {
		// TBD: Optimise
		for (Expression e : asserts.keySet()) {
			BoolExpr px = context.mkBoolConst("q" + counter++);
			// px is the predicate name (in Context object)
			// e is the Green expression of the assertion/clause
			coreClauseMapping.put(px, e);
		}
		return coreClauseMapping;
	}

	public Map<Variable, Expr> getVariableMap() {
		return v2e;
	}

	public int getVariableCount() {
		return v2e.size();
	}

	public Map<Expression, Expr> getAsserts() {
		return asserts;
	}

	@Override
	public void postVisit(IntConstant constant) {
		try {
			stack.push(context.mkBV(constant.getValue(), size));
		} catch (Z3Exception e) {
			e.printStackTrace();
		}
	}

	/*
	 * @Override public void postVisit(IntegerConstant constant) { try {
	 * stack.push(context.mkBV(constant.getValue(), constant.getSize())); } catch
	 * (Z3Exception e) { e.printStackTrace(); } }
	 */

	@Override
	public void postVisit(RealConstant constant) {
		try {
			stack.push(context.mkReal(Double.toString(constant.getValue())));
		} catch (Z3Exception e) {
			e.printStackTrace();
		}
	}

	@Override
	public void postVisit(IntVariable variable) {
		BitVecExpr v = (BitVecExpr) v2e.get(variable);
		if (v == null) {
			Integer lower = variable.getLowerBound();
			Integer upper = variable.getUpperBound();
			try {
				v = context.mkBVConst(variable.getName(), size);
				// now add bounds
				BoolExpr low = context.mkBVSGE(v, context.mkBV(lower, size));
				Operation eLow = new Operation(Operation.Operator.GE, variable, new IntConstant(lower));
				asserts.put(eLow, low);

				BoolExpr high = context.mkBVSLE(v, context.mkBV(upper, size));
				Operation eHigh = new Operation(Operation.Operator.GE, variable, new IntConstant(upper));
				asserts.put(eHigh, high);

				BoolExpr domain = context.mkAnd(low, high);
				domains.add(context.mkAnd(low, high));
				asserts.put(new Operation(Operation.Operator.AND, eLow, eHigh), domain); // This one is needed
			} catch (Z3Exception e) {
				e.printStackTrace();
			}
			v2e.put(variable, v);
		}
		stack.push(v);
	}

	/*
	 * @Override public void postVisit(IntegerVariable variable) { BitVecExpr v =
	 * (BitVecExpr) v2e.get(variable); if (v == null) { Long lower =
	 * variable.getLowerBound(); Long upper = variable.getUpperBound(); Integer size
	 * = variable.getSize(); try { v = context.mkBVConst(variable.getName(), size);
	 * // now add bounds BoolExpr low = context.mkBVSGE(v, context.mkBV(lower,
	 * size)); Operation eLow = new Operation(Operation.Operator.GE, variable, new
	 * IntegerConstant(lower, size)); asserts.put(eLow, low);
	 * 
	 * BoolExpr high = context.mkBVSLE(v, context.mkBV(upper, size)); Operation
	 * eHigh = new Operation(Operation.Operator.GE, variable, new
	 * IntegerConstant(upper, size)); asserts.put(eHigh, high);
	 * 
	 * BoolExpr domain = context.mkAnd(low,high);
	 * domains.add(context.mkAnd(low,high)); asserts.put(new
	 * Operation(Operation.Operator.AND, eLow, eHigh), domain); // This one is
	 * needed } catch (Z3Exception e) { e.printStackTrace(); } v2e.put(variable, v);
	 * } stack.push(v); }
	 */

	@Override
	public void postVisit(RealVariable variable) {
		Expr v = v2e.get(variable);
		if (v == null) {
			Double lower = variable.getLowerBound();
			Double upper = variable.getUpperBound();
			try {
				// TBD: Add Asserts
				if (size == 32) {
					v = context.mkConst(variable.getName(), context.mkFPSort32());
					// now add bounds
					BoolExpr low = context.mkFPGt((FPExpr) v, context.mkFP(lower, context.mkFPSort32()));
					BoolExpr high = context.mkFPLt((FPExpr) v, context.mkFP(upper, context.mkFPSort32()));
					domains.add(context.mkAnd(low, high));
				} else {
					v = context.mkConst(variable.getName(), context.mkFPSortDouble());
					// now add bounds
					BoolExpr low = context.mkFPGt((FPExpr) v, context.mkFP(lower, context.mkFPSortDouble()));
					BoolExpr high = context.mkFPLt((FPExpr) v, context.mkFP(upper, context.mkFPSortDouble()));
					domains.add(context.mkAnd(low, high));
				}

			} catch (Z3Exception e) {
				e.printStackTrace();
			}
			v2e.put(variable, v);
		}
		stack.push(v);
	}

	@Override
	public void postVisit(Operation operation) throws VisitorException {
		Expr l = null;
		Expr r = null;
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
		assert l != null;
		assert r != null;
		try {
			switch (operation.getOperator()) {
			case NOT:
				Expr not = context.mkBVNot((BitVecExpr) l);
				asserts.put(operation, not);
				stack.push(not);
				break;
			case EQ:
				Expr eq = context.mkEq(l, r);
				asserts.put(operation, eq);
				stack.push(eq);
				break;
			case NE:
				Expr ne = context.mkNot(context.mkEq(l, r));
				asserts.put(operation, ne);
				stack.push(ne);
				break;
			case LT:
				Expr lt = null;
				if (l instanceof ArithExpr && r instanceof ArithExpr) {
					lt = context.mkLt((ArithExpr) l, (ArithExpr) r);
				} else if (l instanceof ArithExpr && r instanceof BitVecExpr) {
					System.out.println("##@!@");
				} else if (l instanceof BitVecExpr && r instanceof ArithExpr) {
					System.out.println("##@!@");
				} else if (l instanceof BitVecExpr && r instanceof BitVecExpr) {
					lt = context.mkBVSLT((BitVecExpr) l, (BitVecExpr) r);
				}
				asserts.put(operation, lt);
				stack.push(lt);

				break;
			case LE:
				Expr le = null;
				if (l instanceof ArithExpr && r instanceof ArithExpr) {
					le = context.mkLe((ArithExpr) l, (ArithExpr) r);
				} else if (l instanceof ArithExpr && r instanceof BitVecExpr) {
					System.out.println("##@!@");
				} else if (l instanceof BitVecExpr && r instanceof ArithExpr) {
					System.out.println("##@!@");
				} else if (l instanceof BitVecExpr && r instanceof BitVecExpr) {
					le = context.mkBVSLE((BitVecExpr) l, (BitVecExpr) r);
				}
				asserts.put(operation, le);
				stack.push(le);
				break;
			case GT:
				Expr gt = null;
				if (l instanceof ArithExpr && r instanceof ArithExpr) {
					gt = context.mkGt((ArithExpr) l, (ArithExpr) r);
				} else if (l instanceof ArithExpr && r instanceof BitVecExpr) {
					System.out.println("##@!@");
				} else if (l instanceof BitVecExpr && r instanceof ArithExpr) {
					System.out.println("##@!@");
				} else if (l instanceof BitVecExpr && r instanceof BitVecExpr) {
					gt = context.mkBVSGT((BitVecExpr) l, (BitVecExpr) r);
				}
				asserts.put(operation, gt);
				stack.push(gt);
				break;
			case GE:
				Expr ge = null;
				if (l instanceof ArithExpr && r instanceof ArithExpr) {
					ge = context.mkGe((ArithExpr) l, (ArithExpr) r);
				} else if (l instanceof ArithExpr && r instanceof BitVecExpr) {
					System.out.println("##@!@");
				} else if (l instanceof BitVecExpr && r instanceof ArithExpr) {
					System.out.println("##@!@");
				} else if (l instanceof BitVecExpr && r instanceof BitVecExpr) {
					ge = context.mkBVSGE((BitVecExpr) l, (BitVecExpr) r);
				}
				asserts.put(operation, ge);
				stack.push(ge);
				break;
			case AND:
				Expr and = null;
				if (l instanceof BoolExpr && r instanceof BoolExpr) {
					and = context.mkAnd((BoolExpr) l, (BoolExpr) r);
				} else if (l instanceof BoolExpr && r instanceof BitVecExpr) {
					System.out.println("##@!@");
				} else if (l instanceof BitVecExpr && r instanceof BoolExpr) {
					System.out.println("##@!@");
				} else if (l instanceof BitVecExpr && r instanceof BitVecExpr) {
					and = context.mkBVAND((BitVecExpr) l, (BitVecExpr) r);
				}
				asserts.put(operation, and);
				stack.push(and);
				break;
			case OR:
				Expr or = context.mkBVOR((BitVecExpr) l, (BitVecExpr) r);
				asserts.put(operation, or);
				stack.push(or);
				break;
//			case IMPLIES:
//				stack.push(context.mkImplies(l, r));
//				break;
			case ADD:
				stack.push(context.mkBVAdd((BitVecExpr) l, (BitVecExpr) r));
				break;
			case SUB:
				stack.push(context.mkBVSub((BitVecExpr) l, (BitVecExpr) r));
				break;
			case MUL:
				stack.push(context.mkBVMul((BitVecExpr) l, (BitVecExpr) r));
				break;
			case DIV:
				stack.push(context.mkBVSDiv((BitVecExpr) l, (BitVecExpr) r));
				break;
			case MOD:
				stack.push(context.mkBVSMod((BitVecExpr) l, (BitVecExpr) r));
				break;
			default:
				throw new TranslatorUnsupportedOperation("unsupported operation " + operation.getOperator());
			}
		} catch (Z3Exception e) {
			e.printStackTrace();
		}
	}
}
