/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.z3javabv;

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
import com.microsoft.z3.FPNum;
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
 * Expressions are translated to bitvector operations.
 */
public class Z3JavaBVTranslator extends Visitor {

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
	 * Size of bitvectors.
	 */
	protected final int bitVectorSize;

	/**
	 * Counter for the number of predicates.
	 */
	protected int counter = 0;

	/**
	 * Create an instance of the translator.
	 * 
	 * @param context
	 *                Z3 context
	 */
	public Z3JavaBVTranslator(Context context, int bitvectorSize) {
		this.z3Context = context;
		this.bitVectorSize = bitvectorSize;
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
	public Map<BoolExpr, Expression> getCoreClauseMapping() {
		assertions.forEach((k, v) -> coreClauseMapping.put(z3Context.mkBoolConst(CLAUSE_PREFIX + counter++), k));
		return coreClauseMapping;
	}

	@Override
	public void postVisit(IntConstant constant) {
		try {
			stack.push(z3Context.mkBV(constant.getValue(), bitVectorSize));
		} catch (Z3Exception e) {
			e.printStackTrace();
		}
	}

	@Override
	public void postVisit(RealConstant constant) {
		try {
			stack.push(z3Context.mkReal(Double.toString(constant.getValue())));
		} catch (Z3Exception e) {
			e.printStackTrace();
		}
	}

	/**
	 * Create the Z3 library object that for a given integer variable. Also create
	 * assertions that express the upper and lower bounds on values that the
	 * variable can assume. The integer object is a bitvector with
	 * {@link #bitVectorSize} bits.
	 *
	 * @param variable
	 *                 integer variable to process
	 *
	 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.IntVariable)
	 */
	@Override
	public void postVisit(IntVariable variable) {
		BitVecExpr var = (BitVecExpr) variableMapping.get(variable);
		if (var == null) {
			int lower = variable.getLowerBound();
			int upper = variable.getUpperBound();
			try {
				var = z3Context.mkBVConst(variable.getName(), bitVectorSize);
				BoolExpr lowerBound = z3Context.mkBVSGE(var, z3Context.mkBV(lower, bitVectorSize));
				Operation low = new Operation(Operation.Operator.GE, variable, new IntConstant(lower));
				assertions.put(low, lowerBound);
				BoolExpr upperBound = z3Context.mkBVSLE(var, z3Context.mkBV(upper, bitVectorSize));
				Operation upp = new Operation(Operation.Operator.LE, variable, new IntConstant(upper));
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

	/**
	 * Create the Z3 library object that for a given real variable. Also create
	 * assertions that express the upper and lower bounds on values that the
	 * variable can assume. The size of the real variable object depends on
	 * {@link #bitVectorSize}: it will be either 16, 32, 64, or 128.
	 *
	 * @param variable
	 *                 real variable to process
	 *
	 * @see za.ac.sun.cs.green.expr.Visitor#postVisit(za.ac.sun.cs.green.expr.RealVariable)
	 */
	@Override
	public void postVisit(RealVariable variable) {
		Expr v = variableMapping.get(variable);
		if (v == null) {
			double lower = variable.getLowerBound();
			double upper = variable.getUpperBound();
			try {
				FPNum l = null, u = null;
				switch (bitVectorSize) {
				case 16:
					v = z3Context.mkConst(variable.getName(), z3Context.mkFPSort16());
					l = z3Context.mkFP(lower, z3Context.mkFPSort16());
					u = z3Context.mkFP(upper, z3Context.mkFPSort16());
					break;
				case 32:
					v = z3Context.mkConst(variable.getName(), z3Context.mkFPSort32());
					l = z3Context.mkFP(lower, z3Context.mkFPSort32());
					u = z3Context.mkFP(upper, z3Context.mkFPSort32());
					break;
				case 64:
					v = z3Context.mkConst(variable.getName(), z3Context.mkFPSort64());
					l = z3Context.mkFP(lower, z3Context.mkFPSort64());
					u = z3Context.mkFP(upper, z3Context.mkFPSort64());
					break;
				default:
					v = z3Context.mkConst(variable.getName(), z3Context.mkFPSort128());
					l = z3Context.mkFP(lower, z3Context.mkFPSort128());
					u = z3Context.mkFP(upper, z3Context.mkFPSort128());
					break;
				}
				BoolExpr low = z3Context.mkFPGEq((FPExpr) v, l);
				BoolExpr high = z3Context.mkFPLEq((FPExpr) v, u);
				variableBounds.add(z3Context.mkAnd(low, high));
			} catch (Z3Exception e) {
				e.printStackTrace();
			}
			variableMapping.put(variable, v);
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
				Expr not = null;
				if (l instanceof BitVecExpr) {
					not = z3Context.mkBVNot((BitVecExpr) l);
				} else if ((l instanceof BoolExpr) && (r instanceof BoolExpr)) {
					not = z3Context.mkNot((BoolExpr) l);
					assertions.put(operation, (BoolExpr) not);
				} else {
					throw new Z3JavaBVTranslatorUnsupportedOperation(
							"unsupported operands, operation==" + operation.getOperator());
				}
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
				BoolExpr lt = null;
				if ((l instanceof BitVecExpr) && (r instanceof BitVecExpr)) {
					lt = z3Context.mkBVSLT((BitVecExpr) l, (BitVecExpr) r);
				} else if ((l instanceof ArithExpr) && (r instanceof ArithExpr)) {
					lt = z3Context.mkLt((ArithExpr) l, (ArithExpr) r);
				} else {
					throw new Z3JavaBVTranslatorUnsupportedOperation(
							"unsupported operands, operation==" + operation.getOperator());
				}
				assertions.put(operation, lt);
				stack.push(lt);
				break;
			case LE:
				BoolExpr le = null;
				if ((l instanceof BitVecExpr) && (r instanceof BitVecExpr)) {
					le = z3Context.mkBVSLE((BitVecExpr) l, (BitVecExpr) r);
				} else if ((l instanceof ArithExpr) && (r instanceof ArithExpr)) {
					le = z3Context.mkLe((ArithExpr) l, (ArithExpr) r);
				} else {
					throw new Z3JavaBVTranslatorUnsupportedOperation(
							"unsupported operands, operation==" + operation.getOperator());
				}
				assertions.put(operation, le);
				stack.push(le);
				break;
			case GT:
				BoolExpr gt = null;
				if ((l instanceof BitVecExpr) && (r instanceof BitVecExpr)) {
					gt = z3Context.mkBVSGT((BitVecExpr) l, (BitVecExpr) r);
				} else if ((l instanceof ArithExpr) && (r instanceof ArithExpr)) {
					gt = z3Context.mkGt((ArithExpr) l, (ArithExpr) r);
				} else {
					throw new Z3JavaBVTranslatorUnsupportedOperation(
							"unsupported operands, operation==" + operation.getOperator());
				}
				assertions.put(operation, gt);
				stack.push(gt);
				break;
			case GE:
				BoolExpr ge = null;
				if ((l instanceof BitVecExpr) && (r instanceof BitVecExpr)) {
					ge = z3Context.mkBVSGE((BitVecExpr) l, (BitVecExpr) r);
				} else if ((l instanceof ArithExpr) && (r instanceof ArithExpr)) {
					ge = z3Context.mkGe((ArithExpr) l, (ArithExpr) r);
				} else {
					throw new Z3JavaBVTranslatorUnsupportedOperation(
							"unsupported operands, operation==" + operation.getOperator());
				}
				assertions.put(operation, ge);
				stack.push(ge);
				break;
			case AND:
				Expr and = null;
				if ((l instanceof BitVecExpr) && (r instanceof BitVecExpr)) {
					and = z3Context.mkBVAND((BitVecExpr) l, (BitVecExpr) r);
				} else if ((l instanceof BoolExpr) && (r instanceof BoolExpr)) {
					and = z3Context.mkAnd((BoolExpr) l, (BoolExpr) r);
					assertions.put(operation, (BoolExpr) and);
				} else {
					throw new Z3JavaBVTranslatorUnsupportedOperation(
							"unsupported operands, operation==" + operation.getOperator());
				}
				stack.push(and);
				break;
			case OR:
				Expr or = null;
				if ((l instanceof BitVecExpr) && (r instanceof BitVecExpr)) {
					or = z3Context.mkBVOR((BitVecExpr) l, (BitVecExpr) r);
				} else if ((l instanceof BoolExpr) && (r instanceof BoolExpr)) {
					or = z3Context.mkAnd((BoolExpr) l, (BoolExpr) r);
					assertions.put(operation, (BoolExpr) or);
				} else {
					throw new Z3JavaBVTranslatorUnsupportedOperation(
							"unsupported operands, operation==" + operation.getOperator());
				}
				stack.push(or);
				break;
			case ADD:
				stack.push(z3Context.mkBVAdd((BitVecExpr) l, (BitVecExpr) r));
				break;
			case SUB:
				stack.push(z3Context.mkBVSub((BitVecExpr) l, (BitVecExpr) r));
				break;
			case MUL:
				stack.push(z3Context.mkBVMul((BitVecExpr) l, (BitVecExpr) r));
				break;
			case DIV:
				stack.push(z3Context.mkBVSDiv((BitVecExpr) l, (BitVecExpr) r));
				break;
			case MOD:
				stack.push(z3Context.mkBVSMod((BitVecExpr) l, (BitVecExpr) r));
				break;
			default:
				throw new Z3JavaBVTranslatorUnsupportedOperation("unsupported operation " + operation.getOperator());
			}
		} catch (Z3Exception e) {
			e.printStackTrace();
		}
	}

}
