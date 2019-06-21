package za.ac.sun.cs.green.service.z3;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import com.microsoft.z3.*;
import za.ac.sun.cs.green.expr.*;

class Z3JavaTranslator extends Visitor {

    private Context context = null;
    private Stack<Expr> stack = null;
    private List<BoolExpr> domains = null;
    private Map<Expression, BoolExpr> asserts = null; // maps the Green expressions to Context expressions
    private Map<BoolExpr, Expression> coreClauseMapping; // maps the Context names to Green expressions
    private Map<Variable, Expr> v2e = null; // maps Green variables to Context format
    private int counter = 0; // counter for the predicate names

    public int getVariableCount() {
        return v2e.size();
    }
    public Map<Expression, BoolExpr> getAsserts() {
        return asserts;
    }

    public Z3JavaTranslator(Context c) {
        this.context = c;
        stack = new Stack<Expr>();
        v2e = new HashMap<Variable, Expr>();
        domains = new LinkedList<>();
        asserts = new HashMap<>();
        coreClauseMapping = new HashMap<>();
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

    public Map<BoolExpr, Expression> getCoreMappings() {
        // TODO: Optimise
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

    @Override
    public void postVisit(IntConstant constant) {
        try {
            stack.push(context.mkInt(constant.getValue()));
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

    @Override
    public void postVisit(IntVariable variable) {
        Expr v = v2e.get(variable);
        if (v == null) {
            Integer lower = variable.getLowerBound();
            Integer upper = variable.getUpperBound();
            try {
                v = context.mkIntConst(variable.getName());
                // now add bounds
                BoolExpr low  = context.mkGe((ArithExpr)v,(ArithExpr)context.mkInt(lower));
                Operation eLow = new Operation(Operation.Operator.GE, variable, new IntConstant(lower));
                asserts.put(eLow, low);
                BoolExpr high = context.mkLe((ArithExpr)v,(ArithExpr)context.mkInt(upper));
                Operation eHigh = new Operation(Operation.Operator.GE, variable, new IntConstant(upper));
                asserts.put(eHigh, high);
                BoolExpr domain = context.mkAnd(low,high);
                domains.add(domain);
                asserts.put(new Operation(Operation.Operator.AND, eLow, eHigh), domain); // This one is needed
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
            int lower = (int) (double) variable.getLowerBound();
            int upper = (int) (double) variable.getUpperBound();
            try {
                // TODO Add Asserts
                v = context.mkRealConst(variable.getName());
                // now add bounds
                BoolExpr low  = context.mkGe((ArithExpr)v,(ArithExpr)context.mkReal(lower));
                BoolExpr high = context.mkLe((ArithExpr)v,(ArithExpr)context.mkReal(upper));
                domains.add(context.mkAnd(low,high));
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
        try {
            switch (operation.getOperator()) {
                case NOT:
                    BoolExpr not = context.mkNot((BoolExpr) l);
                    asserts.put(operation, not);
                    stack.push(not);
                    break;
                case EQ:
                    BoolExpr eq = context.mkEq(l, r);
                    asserts.put(operation, eq);
                    stack.push(eq);
                    break;
                case NE:
                    BoolExpr ne = context.mkNot(context.mkEq(l, r));
                    asserts.put(operation, ne);
                    stack.push(ne);
                    break;
                case LT:
                    BoolExpr lt = context.mkLt((ArithExpr) l, (ArithExpr) r);
                    asserts.put(operation, lt);
                    stack.push(lt);
                    break;
                case LE:
                    BoolExpr le = context.mkLe((ArithExpr) l, (ArithExpr) r);
                    asserts.put(operation, le);
                    stack.push(le);
                    break;
                case GT:
                    BoolExpr gt = context.mkGt((ArithExpr) l, (ArithExpr) r);
                    asserts.put(operation, gt);
                    stack.push(gt);
                    break;
                case GE:
                    BoolExpr ge = context.mkGe((ArithExpr) l, (ArithExpr) r);
                    asserts.put(operation, ge);
                    stack.push(ge);
                    break;
                case AND:
                    BoolExpr and = context.mkAnd((BoolExpr) l, (BoolExpr) r);
                    asserts.put(operation, and);
                    stack.push(and);
                    break;
                case OR:
                    BoolExpr or = context.mkOr((BoolExpr) l, (BoolExpr) r);
                    asserts.put(operation, or);
                    stack.push(or);
                    break;
                case IMPLIES:
                    stack.push(context.mkImplies((BoolExpr) l, (BoolExpr) r));
                    break;
                case ADD:
                    stack.push(context.mkAdd((ArithExpr) l, (ArithExpr) r));
                    break;
                case SUB:
                    stack.push(context.mkSub((ArithExpr) l, (ArithExpr) r));
                    break;
                case MUL:
                    stack.push(context.mkMul((ArithExpr) l, (ArithExpr) r));
                    break;
                case DIV:
                    stack.push(context.mkDiv((ArithExpr) l, (ArithExpr) r));
                    break;
                case MOD:
                    stack.push(context.mkMod((IntExpr) l, (IntExpr) r));
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