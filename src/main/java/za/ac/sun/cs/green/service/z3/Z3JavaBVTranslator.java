package za.ac.sun.cs.green.service.z3;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import com.microsoft.z3.*;
import za.ac.sun.cs.green.expr.*;

class Z3JavaBVTranslator extends Visitor {
	
	private Context context = null;
	private Stack<Expr> stack = null;
	private List<BoolExpr> domains = null;
	private Map<Variable, Expr> v2e = null;

	public Z3JavaBVTranslator(Context c) {
		this.context = c;
		stack = new Stack<Expr>();
		v2e = new HashMap<Variable, Expr>();
		domains = new LinkedList<BoolExpr>();
	}

	public BoolExpr getTranslation() {
		BoolExpr result = (BoolExpr)stack.pop();
		/* not required due to Bounder being used */
		/* not sure why this was commented out, it is clearly wrong, with or without bounder */
		for (BoolExpr expr : domains) {
			try {
				result = context.mkAnd(result,expr);
			} catch (Z3Exception e) {
				e.printStackTrace();
			}
		}
		/* was end of old comment */
		return result;
	}
	
	public Map<Variable, Expr> getVariableMap() {
		return v2e;
	}

	@Override
	public void postVisit(IntegerConstant constant) {
		try {
			stack.push(context.mkBV(constant.getValue(), constant.getSize()));
		} catch (Z3Exception e) {
			e.printStackTrace();
		}
	}

	@Override
	public void postVisit(RealConstant constant) {
		try {
			stack.push(context.mkReal(Double.toString(constant.getValue())));
		} catch (Z3Exception e) {
			e.printStackTrace();
		}
	}

//	@Override
//	public void postVisit(IntVariable variable) {
//        BitVecExpr v = v2e.get(variable);
//		if (v == null) {
//			Integer lower = variable.getLowerBound();
//			Integer upper = variable.getUpperBound();
//			try {
//				v = context.mkBV(variable.getName(), 0);
//				// now add bounds
//				BoolExpr low  = context.mkGe((ArithExpr)v,(ArithExpr)context.mkInt(lower));
//				BoolExpr high = context.mkLe((ArithExpr)v,(ArithExpr)context.mkInt(upper));
//				domains.add(context.mkAnd(low,high));
//			} catch (Z3Exception e) {
//				e.printStackTrace();
//			}
//			v2e.put(variable, v);
//		}
//		stack.push(v);
//	}

    @Override
    public void postVisit(IntegerVariable variable) {
        BitVecExpr v = (BitVecExpr) v2e.get(variable);
        if (v == null) {
            Long lower = variable.getLowerBound();
            Long upper = variable.getUpperBound();
            Integer size = variable.getSize();
            try {
                v = context.mkBVConst(variable.getName(), size);
                // now add bounds
                BoolExpr low  = context.mkBVSGE(v, context.mkBV(lower, size));
                BoolExpr high = context.mkBVSLE(v, context.mkBV(upper, size));
                domains.add(context.mkAnd(low,high));
            } catch (Z3Exception e) {
                e.printStackTrace();
            }
            v2e.put(variable, v);
        }
        stack.push(v);
    }

	@Override
	public void postVisit(RealVariable variable) {
		Expr v = v2e.get(variable);
		if (v == null) {
			Double lower = variable.getLowerBound();
			Double upper = variable.getUpperBound();
			int size = variable.getSize();
			try {
			    if (size == 32) {
                    v = context.mkConst(variable.getName(), context.mkFPSort32());
                    // now add bounds
                    BoolExpr low  = context.mkFPGt((FPExpr) v, context.mkFP(lower, context.mkFPSort32()));
                    BoolExpr high = context.mkFPLt((FPExpr) v, context.mkFP(upper, context.mkFPSort32()));
                    domains.add(context.mkAnd(low,high));
                } else {
                    v = context.mkConst(variable.getName(), context.mkFPSortDouble());
                    // now add bounds
                    BoolExpr low  = context.mkFPGt((FPExpr) v, context.mkFP(lower, context.mkFPSortDouble()));
                    BoolExpr high = context.mkFPLt((FPExpr) v, context.mkFP(upper, context.mkFPSortDouble()));
                    domains.add(context.mkAnd(low,high));
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
                stack.push(context.mkBVNot((BitVecExpr) l));
				break;
			case EQ:
				stack.push(context.mkEq(l, r));
				break;
			case NE:
				stack.push(context.mkNot(context.mkEq(l, r)));
				break;
			case LT:
                stack.push(context.mkBVSLT((BitVecExpr) l, (BitVecExpr) r));
				break;
			case LE:
			    if (l instanceof ArithExpr && r instanceof ArithExpr) {
                    stack.push(context.mkLe((ArithExpr) l, (ArithExpr) r));
                } else if (l instanceof BoolExpr && r instanceof BitVecExpr) {
//                    stack.push(context.mkLe((ArithExpr) l, (BitVecExpr) r));
                    System.out.println("##@!@");
                } else if (l instanceof BitVecExpr && r instanceof BoolExpr) {
//                    stack.push(context.mkLe((BitVecExpr) l, (BitVecExpr) r));
                    System.out.println("##@!@");
                } else if (l instanceof BitVecExpr && r instanceof BitVecExpr) {
                    stack.push(context.mkBVSLE((BitVecExpr) l, (BitVecExpr) r));
                }
				break;
			case GT:
				stack.push(context.mkBVSGT((BitVecExpr) l, (BitVecExpr) r));
				break;
			case GE:
                if (l instanceof ArithExpr && r instanceof ArithExpr) {
                    stack.push(context.mkGe((ArithExpr) l, (ArithExpr) r));
                } else if (l instanceof BoolExpr && r instanceof BitVecExpr) {
                    System.out.println("##@!@");
                } else if (l instanceof BitVecExpr && r instanceof BoolExpr) {
                    System.out.println("##@!@");
                } else if (l instanceof BitVecExpr && r instanceof BitVecExpr) {
                    stack.push(context.mkBVSGE((BitVecExpr) l, (BitVecExpr) r));
                }
				break;
			case AND:
			    if (l instanceof BoolExpr && r instanceof BoolExpr) {
                    stack.push(context.mkAnd((BoolExpr) l, (BoolExpr) r));
                } else if (l instanceof BoolExpr && r instanceof BitVecExpr) {
//                    stack.push(context.mkBVAND((BitVecExpr) l, (BitVecExpr) r));
                    System.out.println("##@!@");
                } else if (l instanceof BitVecExpr && r instanceof BoolExpr) {
                    System.out.println("##@!@");
                } else if (l instanceof BitVecExpr && r instanceof BitVecExpr) {
                    stack.push(context.mkBVAND((BitVecExpr) l, (BitVecExpr) r));
                }
				break;
			case OR:
				stack.push(context.mkBVOR((BitVecExpr) l, (BitVecExpr) r));
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
			default:
				throw new TranslatorUnsupportedOperation(
						"unsupported operation " + operation.getOperator());
			}
		} catch (Z3Exception e) {
			e.printStackTrace();
		}
	}
}