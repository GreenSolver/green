package za.ac.sun.cs.green.parser.isl;

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
 *               Description: Parser for the isl output of Barvinok.
 */
public class Parser {

	private HashMap<Expression, Expression> cases;
	private final Scanner s;

	public Parser(Scanner scanner) {
		this.s = scanner;
		init();
	}

	public Parser(String input) {
		this.s = new Scanner(input);
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
		if (s.next() == Scanner.LBRACKET) {
			parseParams();
			s.expect(Scanner.ARROW);
		}
		s.expect(Scanner.LBRACE);
		parseBody(cases);
		while (s.next() == Scanner.SEMICOLON) {
			s.expect(Scanner.SEMICOLON);
			parseBody(cases);
		}
		s.expect(Scanner.RBRACE);
	}

	/**
	 * Function from EBNF: params ::= "[" variable { "," variable } "]"
	 */
	private void parseParams() {
		s.expect(Scanner.LBRACKET);
		s.expect(Scanner.VARIABLE);
		while (s.next() == Scanner.COMMA) {
			s.expect(Scanner.COMMA);
			s.expect(Scanner.VARIABLE);
		}
		s.expect(Scanner.RBRACKET);
	}

	/**
	 * Function from EBNF: body ::= expr [ ":" expr ]
	 * 
	 * @param cases A map to map cases to formulas.
	 */
	private void parseBody(HashMap<Expression, Expression> cases) {
		Expression caseValue = parseExpr();
		if (s.next() == Scanner.COLON) {
			s.expect(Scanner.COLON);
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
			if (s.next() == Scanner.AND) {
				s.expect(Scanner.AND);
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
			if (s.next() == Scanner.EQ) {
				s.expect(Scanner.EQ);
				r = parseExpr1();
				l = new Operation(Operation.Operator.EQ, l, r);
			} else if (s.next() == Scanner.LT) {
				s.expect(Scanner.LT);
				r = parseExpr1();
				l = new Operation(Operation.Operator.LT, l, r);
			} else if (s.next() == Scanner.LE) {
				s.expect(Scanner.LE);
				r = parseExpr1();
				l = new Operation(Operation.Operator.LE, l, r);
			} else if (s.next() == Scanner.GT) {
				s.expect(Scanner.GT);
				r = parseExpr1();
				l = new Operation(Operation.Operator.GT, l, r);
			} else if (s.next() == Scanner.GE) {
				s.expect(Scanner.GE);
				r = parseExpr1();
				l = new Operation(Operation.Operator.GE, l, r);
			} else if (s.next() == Scanner.NE) {
				s.expect(Scanner.NE);
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
			if (s.next() == Scanner.PLUS) {
				s.expect(Scanner.PLUS);
				Expression r = parseTerm();
				l = new Operation(Operation.Operator.ADD, l, r);
			} else if (s.next() == Scanner.MINUS) {
				s.expect(Scanner.MINUS);
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
			if (s.next() == Scanner.MUL) {
				s.expect(Scanner.MUL);
				Expression r = parseTerm1();
				l = new Operation(Operation.Operator.MUL, l, r);
			} else if (s.next() == Scanner.DIV) {
				s.expect(Scanner.DIV);
				Expression r = parseTerm1();
				l = new Operation(Operation.Operator.DIV, l, r);
			} else if (s.next() == Scanner.VARIABLE || s.next() == Scanner.LPAREN || s.next() == Scanner.FLOOR) {
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
			if (s.next() == Scanner.POW) {
				s.expect(Scanner.POW);
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
		if (s.next() == Scanner.INTEGER) {
			int i = s.expectInteger();
			l = new IntConstant(i);
		} else if (s.next() == Scanner.VARIABLE) {
			String v = s.expectVariable();
			l = new IntVariable(v, Integer.MIN_VALUE, Integer.MAX_VALUE);
		} else if (s.next() == Scanner.FLOOR) {
			s.expect(Scanner.FLOOR);
			l = parseFloor();
		} else if (s.next() == Scanner.LPAREN) {
			s.expect(Scanner.LPAREN);
			l = parseExpr();
			s.expect(Scanner.RPAREN);
		} else if (s.next() == Scanner.MINUS) {
			s.expect(Scanner.MINUS);
			l = parseExpr();
		} else if (s.next() == Scanner.NOT) {
			s.expect(Scanner.NOT);
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
		if (s.next() == Scanner.LPAREN) {
			s.expect(Scanner.LPAREN);
			l = parseExpr();
			l = new Operation(Operation.Operator.FLOOR, l);
			s.expect(Scanner.RPAREN);
		} else {
			throw new RuntimeException("expected a left parenthesis");
		}
		return l;
	}
}
