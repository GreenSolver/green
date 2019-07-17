package za.ac.sun.cs.green.service.barvinok;

import java.util.HashMap;

import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;

/**
 * @date: 2018/10/10
 * @author: JH Taljaard.
 * @contributor: Jaco Geldenhuys
 *
 *               Description: ISLParser for the isl output of Barvinok.
 */
public class ISLParser {

	private HashMap<Expression, Expression> cases;
	private final ISLScanner s;

	public ISLParser(ISLScanner scanner) {
		this.s = scanner;
		init();
	}

	public ISLParser(String input) {
		this.s = new ISLScanner(input);
		init();
	}

	/**
	 * Initialize a new map for parser.
	 */
	private void init() {
		cases = new HashMap<>();
	}

	public HashMap<Expression, Expression> getCases() {
		return cases;
	}

	public void parse() {
		parseOutput();
	}

	/**
	 * Function from EBNF: output ::= [ params "->" ] "{" body { ";" body } "}"
	 */
	private void parseOutput() {
		if (s.next() == ISLScanner.LBRACKET) {
			parseParams();
			s.expect(ISLScanner.ARROW);
		}
		s.expect(ISLScanner.LBRACE);
		parseBody(cases);
		while (s.next() == ISLScanner.SEMICOLON) {
			s.expect(ISLScanner.SEMICOLON);
			parseBody(cases);
		}
		s.expect(ISLScanner.RBRACE);
	}

	/**
	 * Function from EBNF: params ::= "[" variable { "," variable } "]"
	 */
	private void parseParams() {
		s.expect(ISLScanner.LBRACKET);
		s.expect(ISLScanner.VARIABLE);
		while (s.next() == ISLScanner.COMMA) {
			s.expect(ISLScanner.COMMA);
			s.expect(ISLScanner.VARIABLE);
		}
		s.expect(ISLScanner.RBRACKET);
	}

	/**
	 * Function from EBNF: body ::= expr [ ":" expr ]
	 * 
	 * @param cases A map to map cases to formulas.
	 */
	private void parseBody(HashMap<Expression, Expression> cases) {
		Expression caseValue = parseExpr();
		if (s.next() == ISLScanner.COLON) {
			s.expect(ISLScanner.COLON);
			Expression caseCondition = parseExpr();
			cases.put(caseCondition, caseValue);
		} else {
			cases.put(Operation.TRUE, caseValue);
		}
	}

	/**
	 * Function from EBNF: expr ::= expr0 { "and" expr0 }
	 * 
	 * @return Green expression.
	 */
	private Expression parseExpr() {
		Expression l = parseExpr0();
		while (true) {
			if (s.next() == ISLScanner.AND) {
				s.expect(ISLScanner.AND);
				Expression r = parseExpr0();
				l = new Operation(Operation.Operator.AND, l, r);
			} else {
				break;
			}
		}
		return l;
	}

	/**
	 * Function from EBNF: expr0 ::= expr1 { equality expr1 }
	 * 
	 * @return Green expression
	 */
	private Expression parseExpr0() {
		Expression l = parseExpr1();
		Expression r;

		while (true) {
			if (s.next() == ISLScanner.EQ) {
				s.expect(ISLScanner.EQ);
				r = parseExpr1();
				l = new Operation(Operation.Operator.EQ, l, r);
			} else if (s.next() == ISLScanner.LT) {
				s.expect(ISLScanner.LT);
				r = parseExpr1();
				l = new Operation(Operation.Operator.LT, l, r);
			} else if (s.next() == ISLScanner.LE) {
				s.expect(ISLScanner.LE);
				r = parseExpr1();
				l = new Operation(Operation.Operator.LE, l, r);
			} else if (s.next() == ISLScanner.GT) {
				s.expect(ISLScanner.GT);
				r = parseExpr1();
				l = new Operation(Operation.Operator.GT, l, r);
			} else if (s.next() == ISLScanner.GE) {
				s.expect(ISLScanner.GE);
				r = parseExpr1();
				l = new Operation(Operation.Operator.GE, l, r);
			} else if (s.next() == ISLScanner.NE) {
				s.expect(ISLScanner.NE);
				r = parseExpr1();
				l = new Operation(Operation.Operator.NE, l, r);
			} else {
				break;
			}
		}
		return l;
	}

	/**
	 * Function from EBNF: expr1 ::= term { ( "+" | "-" ) term }
	 * 
	 * @return Green expression
	 */
	private Expression parseExpr1() {
		Expression l = parseTerm();
		while (true) {
			if (s.next() == ISLScanner.PLUS) {
				s.expect(ISLScanner.PLUS);
				Expression r = parseTerm();
				l = new Operation(Operation.Operator.ADD, l, r);
			} else if (s.next() == ISLScanner.MINUS) {
				s.expect(ISLScanner.MINUS);
				Expression r = parseTerm();
				l = new Operation(Operation.Operator.SUB, l, r);
			} else {
				break;
			}
		}
		return l;
	}

	/**
	 * Function from EBNF: term ::= term1 { ( "*" | "/" | "empty" ) term1 }
	 * 
	 * @return Green Expression
	 */
	private Expression parseTerm() {
		Expression l = parseTerm1();
		while (true) {
			if (s.next() == ISLScanner.MUL) {
				s.expect(ISLScanner.MUL);
				Expression r = parseTerm1();
				l = new Operation(Operation.Operator.MUL, l, r);
			} else if (s.next() == ISLScanner.DIV) {
				s.expect(ISLScanner.DIV);
				Expression r = parseTerm1();
				l = new Operation(Operation.Operator.DIV, l, r);
			} else if (s.next() == ISLScanner.VARIABLE || s.next() == ISLScanner.LPAREN || s.next() == ISLScanner.FLOOR) {
				l = parseTerm1();
			} else {
				break;
			}
		}
		return l;
	}

	/**
	 * From EBNF: term1 ::= factor { "^" factor }
	 * 
	 * @return Green Expression
	 */
	private Expression parseTerm1() {
		Expression l = parseFactor();
		while (true) {
			if (s.next() == ISLScanner.POW) {
				s.expect(ISLScanner.POW);
				Expression r = parseFactor();
				l = new Operation(Operation.Operator.POWER, l, r);
			} else {
				break;
			}
		}
		return l;
	}

	/**
	 * Function from EBNF: factor ::= integer | variable | floor | "(" expr ")" |
	 * "-" expr | "not" expr
	 * 
	 * @return Green Expression
	 */
	private Expression parseFactor() {
		Expression l;
		if (s.next() == ISLScanner.INTEGER) {
			int i = s.expectInteger();
			l = new IntConstant(i);
		} else if (s.next() == ISLScanner.VARIABLE) {
			String v = s.expectVariable();
			l = new IntVariable(v, Integer.MIN_VALUE, Integer.MAX_VALUE);
		} else if (s.next() == ISLScanner.FLOOR) {
			s.expect(ISLScanner.FLOOR);
			l = parseFloor();
		} else if (s.next() == ISLScanner.LPAREN) {
			s.expect(ISLScanner.LPAREN);
			l = parseExpr();
			s.expect(ISLScanner.RPAREN);
		} else if (s.next() == ISLScanner.MINUS) {
			s.expect(ISLScanner.MINUS);
			l = parseExpr();
		} else if (s.next() == ISLScanner.NOT) {
			s.expect(ISLScanner.NOT);
			l = parseExpr();
			l = new Operation(Operation.Operator.NOT, l);
		} else {
			throw new RuntimeException("expected an expression");
		}

		return l;
	}

	/**
	 * From EBNF: floor ::= "floor" "(" expr ")"
	 * 
	 * @return Green Expression
	 */
	private Expression parseFloor() {
		Expression l;
		if (s.next() == ISLScanner.LPAREN) {
			s.expect(ISLScanner.LPAREN);
			l = parseExpr();
			l = new Operation(Operation.Operator.FLOOR, l);
			s.expect(ISLScanner.RPAREN);
		} else {
			throw new RuntimeException("expected a left parenthesis");
		}
		return l;
	}
}
