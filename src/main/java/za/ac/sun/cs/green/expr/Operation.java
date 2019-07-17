/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.expr;

import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * Representation of an operation with one operators and one or more operands.
 */
public class Operation extends Expression {

	/**
	 * Required for serialization.
	 */
	private static final long serialVersionUID = -7494964897567521035L;

	/**
	 * Position of operators.
	 */
	public enum Fix {
		PREFIX, INFIX, POSTFIX;
	}

	/**
	 * Available operators.
	 */
	public enum Operator {
		// @formatter:off
		EQ("==", 2, Fix.INFIX),
		NE("!=", 2, Fix.INFIX),
		LT("<", 2, Fix.INFIX),
		LE("<=", 2, Fix.INFIX),
		GT(">", 2, Fix.INFIX),
		GE(">=", 2, Fix.INFIX),
		AND("&&", 2, Fix.INFIX),
		OR("||", 2, Fix.INFIX),
		IMPLIES("=>", 2, Fix.INFIX),
		NOT("!", 1, Fix.INFIX),
		ADD("+", 2, Fix.INFIX),
		SUB("-", 2, Fix.INFIX),
		MUL("*", 2, Fix.INFIX),
		DIV("/", 2, Fix.INFIX),
		MOD("%", 2, Fix.INFIX),
		NEG("-", 1, Fix.INFIX),
		BIT_AND("&", 2, Fix.INFIX),
		BIT_OR("|", 2, Fix.INFIX),
		BIT_XOR("^", 2, Fix.INFIX),
		BIT_NOT("~", 1, Fix.INFIX),
		SHIFTL("<<", 2, Fix.INFIX),
		SHIFTR(">>", 2, Fix.INFIX),
		SHIFTUR(">>>", 2, Fix.INFIX),
		BIT_CONCAT("BIT_CONCAT", 2, Fix.PREFIX),
		SIN("SIN", 1),
		COS("COS", 1),
		TAN("TAN", 1),
		ASIN("ASIN", 1),
		ACOS("ACOS", 1),
		ATAN("ATAN", 1),
		ATAN2("ATAN2", 2),
		ROUND("ROUND", 1),
		LOG("LOG", 1),
		EXP("EXP", 1),
		POWER("POWER", 2),
		SQRT("SQRT", 1),
		FLOOR("FLOOR", 1),
		// String Operations
		SUBSTRING("SUBSTRING", 3, Fix.POSTFIX),
		CONCAT("CONCAT", 2, Fix.POSTFIX),
		TRIM("TRIM", 1, Fix.POSTFIX),
		REPLACE("REPLACE", 3, Fix.POSTFIX),
		REPLACEFIRST("REPLACEFIRST", 3, Fix.POSTFIX),
		TOLOWERCASE("TOLOWERCASE", 2, Fix.POSTFIX),
		TOUPPERCASE("TOUPPERCASE", 2, Fix.POSTFIX),
		VALUEOF("VALUEOF", 2, Fix.POSTFIX),
		// String Comparators
		NOTCONTAINS("NOTCONTAINS", 2, Fix.POSTFIX),
		CONTAINS("CONTAINS", 2, Fix.POSTFIX),
		LASTINDEXOFCHAR("LASTINDEXOFCHAR", 3, Fix.POSTFIX),
		LASTINDEXOFSTRING("LASTINDEXOFSTRING", 3, Fix.POSTFIX),
		STARTSWITH("STARTSWITH", 3, Fix.POSTFIX),
		NOTSTARTSWITH("NOTSTARTSWITH", 3, Fix.POSTFIX),
		ENDSWITH("ENDSWITH", 2, Fix.POSTFIX),
		NOTENDSWITH("NOTENDSWITH", 2, Fix.POSTFIX),
		EQUALS("EQUALS", 2, Fix.POSTFIX),
		NOTEQUALS("NOTEQUALS", 2, Fix.POSTFIX),
		EQUALSIGNORECASE("EQUALSIGNORECASE", 2, Fix.POSTFIX),
		NOTEQUALSIGNORECASE("NOTEQUALSIGNORECASE", 2, Fix.POSTFIX),
		EMPTY("EMPTY", 1, Fix.POSTFIX),
		NOTEMPTY("NOTEMPTY", 1, Fix.POSTFIX),
		ISINTEGER("ISINTEGER", 1, Fix.POSTFIX),
		NOTINTEGER("NOTINTEGER", 1, Fix.POSTFIX),
		ISFLOAT("ISFLOAT", 1, Fix.POSTFIX),
		NOTFLOAT("NOTFLOAT", 1, Fix.POSTFIX),
		ISLONG("ISLONG", 1, Fix.POSTFIX),
		NOTLONG("NOTLONG", 1, Fix.POSTFIX),
		ISDOUBLE("ISDOUBLE", 1, Fix.POSTFIX),
		NOTDOUBLE("NOTDOUBLE", 1, Fix.POSTFIX),
		ISBOOLEAN("ISBOOLEAN", 1, Fix.POSTFIX),
		NOTBOOLEAN("NOTBOOLEAN", 1, Fix.POSTFIX),
		REGIONMATCHES("REGIONMATCHES", 6, Fix.POSTFIX),
		NOTREGIONMATCHES("NOTREGIONMATCHES", 6, Fix.POSTFIX);
    	// @formatter:on

		/**
		 * String representation of the operator.
		 */
		private final String string;

		/**
		 * Arity of the operator. If the operator can take a variable number of
		 * operands, the value of this field is the maximum.
		 */
		private final int arity;

		/**
		 * Position of the operator relative to the operands.
		 */
		private final Fix fix;

		/**
		 * Create a new operator with the given string representation and arity. The
		 * default position of {@link Fix#PREFIX} is assumed.
		 * 
		 * @param string
		 *               string representation of the operator
		 * @param arity
		 *               arity of the operator
		 */
		Operator(final String string, final int arity) {
			this.string = string;
			this.arity = arity;
			fix = Fix.PREFIX;
		}

		/**
		 * Create a new operator with the given string representation, arity, and
		 * position.
		 * 
		 * @param string
		 *               string representation of the operator
		 * @param arity
		 *               arity of the operator
		 * @param fix
		 *               position of the operator relative to its operands
		 */
		Operator(final String string, final int arity, final Fix fix) {
			this.string = string;
			this.arity = arity;
			this.fix = fix;
		}

		/**
		 * Return the string representation of the operator.
		 *
		 * @return string representation of the operator
		 *
		 * @see java.lang.Enum#toString()
		 */
		@Override
		public String toString() {
			return string;
		}

		/**
		 * Return the arity of the operator.
		 *
		 * @return arity of the operator
		 */
		public int getArity() {
			return arity;
		}

		/**
		 * Return the position of the operator.
		 *
		 * @return position of the operator
		 */
		public Fix getFix() {
			return fix;
		}

	}

	/**
	 * Integer constant 0.
	 */
	public static final IntConstant ZERO = new IntConstant(0);

	/**
	 * Integer constant 1.
	 */
	public static final IntConstant ONE = new IntConstant(1);

	/**
	 * Expression to represent the boolean constant {@code false}.
	 */
	public static final Expression FALSE = new Operation(Operator.EQ, ZERO, ONE);

	/**
	 * Expression to represent the boolean constant {@code true}.
	 */
	public static final Expression TRUE = new Operation(Operator.EQ, ZERO, ZERO);

	/**
	 * Hash code for this operation. It is only computed once and the initial value
	 * of -1 signifies that it is not yet computed.
	 */
	private int hashCode = -1;

	/**
	 * The operator associated with this operation.
	 */
	private final Operator operator;

	/**
	 * Array of operands for this operation.
	 */
	private final Expression[] operands;

	/**
	 * Construct an operation with the given operator and operands.
	 * 
	 * @param operator
	 *                 operation for this operation
	 * @param operands
	 *                 array of operands for this operation
	 */
	public Operation(final Operator operator, Expression... operands) {
		this.operator = operator;
		this.operands = operands;
	}

	/**
	 * Apply the operator to the operands, simplify constant expression when
	 * feasible, and return the resulting expression.
	 *
	 * @param operator
	 *                 operator to apply
	 * @param operands
	 *                 array of operands to apply operator to
	 * @return resulting expression
	 */
	public static Expression apply(Operator operator, Expression... operands) {
		switch (operator) {
		case ADD:
			long result = 0;
			for (Expression operand : operands) {
				if (operand instanceof IntConstant) {
					result += ((IntConstant) operand).getValue();
				} else {
					return new Operation(operator, operands);
				}
			}
			return new IntConstant((int) result);
		default:
			return new Operation(operator, operands);
		}
	}

	/**
	 * Return the operator of the operation.
	 *
	 * @return operator of the operation
	 */
	public Operator getOperator() {
		return operator;
	}

	/**
	 * Return the number of operands. In most cases, this should be equal to the
	 * arity of the operator.
	 *
	 * @return number of operands
	 */
	public int getOperandCount() {
		return operands.length;
	}

	/**
	 * Return the specified operand.
	 *
	 * @param index
	 *              number of the operand (0, 1, ...)
	 * @return index-th operand
	 */
	public Expression getOperand(int index) {
		if ((index < 0) || (index >= operands.length)) {
			return null;
		} else {
			return operands[index];
		}
	}

	/**
	 * Return an {@link Iterable} instance over the operands.
	 *
	 * @return {@link Iterable} over operands
	 */
	public Iterable<Expression> getOperands() {
		return new Iterable<Expression>() {

			@Override
			public Iterator<Expression> iterator() {
				return new Iterator<Expression>() {

					private int index = 0;

					@Override
					public boolean hasNext() {
						return index < operands.length;
					}

					@Override
					public Expression next() {
						if (index < operands.length) {
							return operands[index++];
						} else {
							throw new NoSuchElementException();
						}
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
			}
		};
	}

	/**
	 * Accept a visitor. It straightforwardly pre-visits the operation, visits each
	 * of the operands in turn, and then post-visits the operation.
	 *
	 * @param visitor
	 *                expression visitor
	 * @throws VisitorException
	 *                          passed on from the visitor
	 *
	 * @see za.ac.sun.cs.green.expr.Expression#accept(za.ac.sun.cs.green.expr.Visitor)
	 */
	@Override
	public void accept(Visitor visitor) throws VisitorException {
		visitor.preVisit(this);
		for (Expression operand : operands) {
			operand.accept(visitor);
		}
		visitor.postVisit(this);
	}

	/**
	 * Checks if this operation is equal to another. Operations are equal if and
	 * only if they have the same operator and same number of operands, and each of
	 * the corresponding operands are equal.
	 *
	 * @param object
	 *               potential operation to compare to
	 * @return {@code true} if and only if the operations are effectively equal
	 *
	 * @see za.ac.sun.cs.green.expr.Expression#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object object) {
		if (object instanceof Operation) {
			Operation operation = (Operation) object;
			if (operator != operation.operator) {
				return false;
			}
			if (operands.length != operation.operands.length) {
				return false;
			}
			for (int i = 0; i < operands.length; i++) {
				if (!operands[i].equals(operation.operands[i])) {
					return false;
				}
			}
			return true;
		} else {
			return false;
		}
	}

	/**
	 * Calculate, if necessary, and return the hash code.
	 *
	 * @return operation hash code
	 *
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		// TODO
		if (hashCode == -1) {
			int h = operator.hashCode();
			for (Expression o : operands) {
				h ^= o.hashCode();
			}
			hashCode = h;
		}
		return hashCode;

	}

	/**
	 * Return a string representation of the operation. This method takes into
	 * account the operator and its position and parentheses for operands.
	 *
	 * @return string representation
	 *
	 * @see za.ac.sun.cs.green.expr.Expression#toString0()
	 */
	@Override
	public String toString0() {
		StringBuilder sb = new StringBuilder();
		int arity = operator.getArity();
		Fix fix = operator.getFix();
		if (arity == 2 && fix == Fix.INFIX) {
			if ((operands[0] instanceof Constant) || (operands[0] instanceof Variable)) {
				sb.append(operands[0].toString());
			} else {
				sb.append('(');
				sb.append(operands[0].toString());
				sb.append(')');
			}
			sb.append(operator.toString());
			if ((operands[1] instanceof Constant) || (operands[1] instanceof Variable)) {
				sb.append(operands[1].toString());
			} else {
				sb.append('(');
				sb.append(operands[1].toString());
				sb.append(')');
			}
		} else if (arity == 1 && fix == Fix.INFIX) {
			sb.append(operator.toString());
			if ((operands[0] instanceof Constant) || (operands[0] instanceof Variable)) {
				sb.append(operands[0].toString());
			} else {
				sb.append('(');
				sb.append(operands[0].toString());
				sb.append(')');
			}
		} else if (fix == Fix.POSTFIX) {
			sb.append(operands[0].toString());
			sb.append('.');
			sb.append(operator.toString());
			sb.append('(');
			if (operands.length > 1) {
				sb.append(operands[1].toString());
				for (int i = 2; i < operands.length; i++) {
					sb.append(',');
					sb.append(operands[i].toString());
				}
			}
			sb.append(')');
		} else if (operands.length > 0) {
			sb.append(operator.toString());
			sb.append('(');
			sb.append(operands[0].toString());
			for (int i = 1; i < operands.length; i++) {
				sb.append(',');
				sb.append(operands[i].toString());
			}
			sb.append(')');
		} else {
			sb.append(operator.toString());
		}
		return sb.toString();
	}

	// ======================================================================
	//
	// STATIC METHODS
	//
	// ======================================================================

	/**
	 * Construct an operation "{@code a == b}".
	 *
	 * @param left
	 *              first operand
	 * @param right
	 *              second operand
	 * @return resulting operation
	 */
	public static Operation eq(Expression left, Expression right) {
		return new Operation(Operator.EQ, left, right);
	}

	/**
	 * Construct an operation "{@code a != b}".
	 *
	 * @param left
	 *              first operand
	 * @param right
	 *              second operand
	 * @return resulting operation
	 */
	public static Operation ne(Expression left, Expression right) {
		return new Operation(Operator.NE, left, right);
	}

	/**
	 * Construct an operation "{@code a < b}".
	 *
	 * @param left
	 *              first operand
	 * @param right
	 *              second operand
	 * @return resulting operation
	 */
	public static Operation lt(Expression left, Expression right) {
		return new Operation(Operator.LT, left, right);
	}

	/**
	 * Construct an operation "{@code a <= b}".
	 *
	 * @param left
	 *              first operand
	 * @param right
	 *              second operand
	 * @return resulting operation
	 */
	public static Operation le(Expression left, Expression right) {
		return new Operation(Operator.LE, left, right);
	}

	/**
	 * Construct an operation "{@code a > b}".
	 *
	 * @param left
	 *              first operand
	 * @param right
	 *              second operand
	 * @return resulting operation
	 */
	public static Operation gt(Expression left, Expression right) {
		return new Operation(Operator.GT, left, right);
	}

	/**
	 * Construct an operation "{@code a >= b}".
	 *
	 * @param left
	 *              first operand
	 * @param right
	 *              second operand
	 * @return resulting operation
	 */
	public static Operation ge(Expression left, Expression right) {
		return new Operation(Operator.GE, left, right);
	}

	/**
	 * Construct an operation "{@code a && b}".
	 *
	 * @param left
	 *              first operand
	 * @param right
	 *              second operand
	 * @return resulting operation
	 */
	public static Operation and(Expression left, Expression right) {
		return new Operation(Operator.AND, left, right);
	}

	/**
	 * Construct an operation "{@code a || b}".
	 *
	 * @param left
	 *              first operand
	 * @param right
	 *              second operand
	 * @return resulting operation
	 */
	public static Operation or(Expression left, Expression right) {
		return new Operation(Operator.OR, left, right);
	}

	/**
	 * Construct an operation "{@code a => b}".
	 *
	 * @param left
	 *              first operand
	 * @param right
	 *              second operand
	 * @return resulting operation
	 */
	public static Operation implies(Expression left, Expression right) {
		return new Operation(Operator.IMPLIES, left, right);
	}

	/**
	 * Construct an operation "{@code !a}".
	 *
	 * @param operand
	 *                single operand of the operation
	 * @return resulting operation
	 */
	public static Operation not(Expression operand) {
		return new Operation(Operator.NOT, operand);
	}

	/**
	 * Construct an operation "{@code a + b}".
	 *
	 * @param left
	 *              first operand
	 * @param right
	 *              second operand
	 * @return resulting operation
	 */
	public static Operation add(Expression left, Expression right) {
		return new Operation(Operator.ADD, left, right);
	}

	/**
	 * Construct an operation "{@code a - b}".
	 *
	 * @param left
	 *              first operand
	 * @param right
	 *              second operand
	 * @return resulting operation
	 */
	public static Operation sub(Expression left, Expression right) {
		return new Operation(Operator.SUB, left, right);
	}

	/**
	 * Construct an operation "{@code a * b}".
	 *
	 * @param left
	 *              first operand
	 * @param right
	 *              second operand
	 * @return resulting operation
	 */
	public static Operation mul(Expression left, Expression right) {
		return new Operation(Operator.MUL, left, right);
	}

	/**
	 * Construct an operation "{@code a / b}".
	 *
	 * @param left
	 *              first operand
	 * @param right
	 *              second operand
	 * @return resulting operation
	 */
	public static Operation div(Expression left, Expression right) {
		return new Operation(Operator.DIV, left, right);
	}

	/**
	 * Construct an operation "{@code a % b}".
	 *
	 * @param left
	 *              first operand
	 * @param right
	 *              second operand
	 * @return resulting operation
	 */
	public static Operation mod(Expression left, Expression right) {
		return new Operation(Operator.MOD, left, right);
	}

	/**
	 * Construct an operation "{@code -a}" (unary minus).
	 *
	 * @param operand
	 *                single operand of the operation
	 * @return resulting operation
	 */
	public static Operation neg(Expression operand) {
		return new Operation(Operator.NEG, operand);
	}

}
