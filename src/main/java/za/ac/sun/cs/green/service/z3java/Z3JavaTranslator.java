package za.ac.sun.cs.green.service.z3java;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.IntExpr;
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

/**
 * Visitor to translate a Green expression to calls to the Z3 Java library.
 */
public class Z3JavaTranslator extends Visitor {

	/**
	 * Prefix used for naming clauses.
	 */
	protected static final String CLAUSE_PREFIX = "q";

	/**
	 * Context of the Z3 solver.
	 */
	protected final Context z3Context;

	/**
	 * Stack of operands.
	 */
	protected final Stack<Expr> stack = new Stack<>();

	/**
	 * List of variable lower and upper bounds as Z3 expressions.
	 */
	protected final List<BoolExpr> variableBounds = new LinkedList<>();

	/**
	 * Mapping of Green expressions to Z3 expressions.
	 */
	protected final Map<Expression, BoolExpr> assertions = new HashMap<>();

	/**
	 * Mapping of Z3 expressions to Green expressions.
	 */
	protected final Map<BoolExpr, Expression> coreClauseMapping = new HashMap<>();

	/**
	 * Mapping of Green variables to corresponding Z3 variables.
	 */
	protected final Map<Variable, Expr> variableMapping = new HashMap<>();

	/**
	 * Counter for the number of predicates.
	 */
	protected int counter = 0;

	/**
	 * Create an instance of the translator.
	 * 
	 * @param context Z3 context
	 */
	public Z3JavaTranslator(Context context) {
		this.z3Context = context;
	}

	/**
	 * Return the number of variables in the last translation.
	 * 
	 * @return number of variables in the last translation
	 */
	public int getVariableCount() {
		return variableMapping.size();
	}

	/**
	 * Return the variable mapping.
	 * 
	 * @return variable mapping
	 */
	public Map<Variable, Expr> getVariableMap() {
		return variableMapping;
	}

	/**
	 * Return the mapping of Green expressions to Z3 expressions.
	 * 
	 * @return mapping of Green expressions to Z3 expressions
	 */
	public Map<Expression, BoolExpr> getAssertions() {
		return assertions;
	}

	/**
	 * Return the conjunction of the Green expression translation and the variable
	 * bounds.
	 * 
	 * @return conjoined Z3 expression
	 */
	public BoolExpr getTranslation() {
		BoolExpr result = (BoolExpr) stack.pop();
		for (BoolExpr expr : variableBounds) {
			try {
				result = z3Context.mkAnd(result, expr);
			} catch (Z3Exception e) {
				e.printStackTrace();
			}
		}
		return result;
	}

	/**
	 * Return the mapping of Z3 expressions to Green expressions.
	 * 
	 * @return mapping of Z3 expressions to Green expressions
	 */
	public Map<BoolExpr, Expression> getCoreClauseMappings() {
		assertions.forEach((k, v) -> coreClauseMapping.put(z3Context.mkBoolConst(CLAUSE_PREFIX + counter++), k));
		return coreClauseMapping;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.
	 * IntConstant)
	 */
	@Override
	public void postVisit(IntConstant constant) {
		try {
			stack.push(z3Context.mkInt(constant.getValue()));
		} catch (Z3Exception e) {
			e.printStackTrace();
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.
	 * RealConstant)
	 */
	@Override
	public void postVisit(RealConstant constant) {
		try {
			stack.push(z3Context.mkReal(Double.toString(constant.getValue())));
		} catch (Z3Exception e) {
			e.printStackTrace();
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.
	 * IntVariable)
	 */
	@Override
	public void postVisit(IntVariable variable) {
		Expr var = variableMapping.get(variable);
		if (var == null) {
			int lower = variable.getLowerBound();
			int upper = variable.getUpperBound();
			try {
				var = z3Context.mkIntConst(variable.getName());
				BoolExpr lowerBound = z3Context.mkGe((ArithExpr) var, (ArithExpr) z3Context.mkInt(lower));
				Operation low = new Operation(Operation.Operator.GE, variable, new IntConstant(lower));
				assertions.put(low, lowerBound);
				BoolExpr upperBound = z3Context.mkLe((ArithExpr) var, (ArithExpr) z3Context.mkInt(upper));
				Operation upp = new Operation(Operation.Operator.GE, variable, new IntConstant(upper));
				assertions.put(upp, upperBound);
				BoolExpr bounds = z3Context.mkAnd(lowerBound, upperBound);
				variableBounds.add(bounds);
				assertions.put(new Operation(Operation.Operator.AND, low, upp), bounds); // This one is needed
			} catch (Z3Exception e) {
				e.printStackTrace();
			}
			variableMapping.put(variable, var);
		}
		stack.push(var);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.
	 * RealVariable)
	 */
	@Override
	public void postVisit(RealVariable variable) {
		Expr v = variableMapping.get(variable);
		if (v == null) {
			int lower = (int) (double) variable.getLowerBound();
			int upper = (int) (double) variable.getUpperBound();
			try {
				v = z3Context.mkRealConst(variable.getName());
				BoolExpr low = z3Context.mkGe((ArithExpr) v, (ArithExpr) z3Context.mkReal(lower));
				BoolExpr high = z3Context.mkLe((ArithExpr) v, (ArithExpr) z3Context.mkReal(upper));
				variableBounds.add(z3Context.mkAnd(low, high));
			} catch (Z3Exception e) {
				e.printStackTrace();
			}
			variableMapping.put(variable, v);
		}
		stack.push(v);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.Operation)
	 */
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
				BoolExpr not = z3Context.mkNot((BoolExpr) l);
				assertions.put(operation, not);
				stack.push(not);
				break;
			case EQ:
				BoolExpr eq = z3Context.mkEq(l, r);
				assertions.put(operation, eq);
				stack.push(eq);
				break;
			case NE:
				BoolExpr ne = z3Context.mkNot(z3Context.mkEq(l, r));
				assertions.put(operation, ne);
				stack.push(ne);
				break;
			case LT:
				BoolExpr lt = z3Context.mkLt((ArithExpr) l, (ArithExpr) r);
				assertions.put(operation, lt);
				stack.push(lt);
				break;
			case LE:
				BoolExpr le = z3Context.mkLe((ArithExpr) l, (ArithExpr) r);
				assertions.put(operation, le);
				stack.push(le);
				break;
			case GT:
				BoolExpr gt = z3Context.mkGt((ArithExpr) l, (ArithExpr) r);
				assertions.put(operation, gt);
				stack.push(gt);
				break;
			case GE:
				BoolExpr ge = z3Context.mkGe((ArithExpr) l, (ArithExpr) r);
				assertions.put(operation, ge);
				stack.push(ge);
				break;
			case AND:
				BoolExpr and = z3Context.mkAnd((BoolExpr) l, (BoolExpr) r);
				assertions.put(operation, and);
				stack.push(and);
				break;
			case OR:
				BoolExpr or = z3Context.mkOr((BoolExpr) l, (BoolExpr) r);
				assertions.put(operation, or);
				stack.push(or);
				break;
			case IMPLIES:
				stack.push(z3Context.mkImplies((BoolExpr) l, (BoolExpr) r));
				break;
			case ADD:
				stack.push(z3Context.mkAdd((ArithExpr) l, (ArithExpr) r));
				break;
			case SUB:
				stack.push(z3Context.mkSub((ArithExpr) l, (ArithExpr) r));
				break;
			case MUL:
				stack.push(z3Context.mkMul((ArithExpr) l, (ArithExpr) r));
				break;
			case DIV:
				stack.push(z3Context.mkDiv((ArithExpr) l, (ArithExpr) r));
				break;
			case MOD:
				stack.push(z3Context.mkMod((IntExpr) l, (IntExpr) r));
				break;
			default:
				throw new Z3JavaTranslatorUnsupportedOperation("unsupported operation " + operation.getOperator());
			}
		} catch (Z3Exception e) {
			e.printStackTrace();
		}
	}

}
