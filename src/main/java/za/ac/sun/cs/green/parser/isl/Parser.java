package za.ac.sun.cs.green.parser.isl;

import za.ac.sun.cs.green.expr.*;
import java.util.HashMap;

/**
 * @date: 2018/10/10
 * @author: JH Taljaard.
 * @contributor: Jaco Geldenhuys
 *
 * Description:
 * Parser for the isl output of Barvinok.
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
     * Function from EBNF:
     * output ::= [ params "->" ] "{" body { ";" body } "}"
     */
    private void parseOutput() {
        if (s.next() == s.LBRACKET) {
            parseParams();
            s.expect(s.ARROW);
        }
        s.expect(s.LBRACE);
        parseBody(cases);
        while (s.next() == s.SEMICOLON) {
            s.expect(s.SEMICOLON);
            parseBody(cases);
        }
        s.expect(s.RBRACE);
    }

    /**
     * Function from EBNF:
     * params ::= "[" variable { "," variable } "]"
     */
    private void parseParams() {
        s.expect(s.LBRACKET);
        s.expect(s.VARIABLE);
        while (s.next() == s.COMMA) {
            s.expect(s.COMMA);
            s.expect(s.VARIABLE);
        }
        s.expect(s.RBRACKET);
    }

    /**
     * Function from EBNF:
     * body ::= expr [ ":" expr ]
     * @param cases A map to map cases to formulas.
     */
    private void parseBody(HashMap<Expression, Expression> cases) {
        Expression caseValue = parseExpr();
        if (s.next() == s.COLON) {
            s.expect(s.COLON);
            Expression caseCondition = parseExpr();
            cases.put(caseCondition, caseValue);
        } else {
            cases.put(Operation.TRUE, caseValue);
        }
    }

    /**
     * Function from EBNF:
     * expr ::= expr0 { "and" expr0 }
     * @return Green expression.
     */
    private Expression parseExpr() {
        Expression l = parseExpr0();
        while (true) {
            if (s.next() == s.AND) {
                s.expect(s.AND);
                Expression r = parseExpr0();
                l = new Operation(Operation.Operator.AND, l, r);
            } else {
                break;
            }
        }
        return l;
    }

    /**
     * Function from EBNF:
     * expr0 ::= expr1 { equality expr1 }
     * @return Green expression
     */
    private Expression parseExpr0() {
        Expression l = parseExpr1();
        Expression r;

        while (true) {
            if (s.next() == s.EQ) {
                s.expect(s.EQ);
                r = parseExpr1();
                l = new Operation(Operation.Operator.EQ, l, r);
            } else if (s.next() == s.LT) {
                s.expect(s.LT);
                r = parseExpr1();
                l = new Operation(Operation.Operator.LT, l, r);
            } else if (s.next() == s.LE) {
                s.expect(s.LE);
                r = parseExpr1();
                l = new Operation(Operation.Operator.LE, l, r);
            } else if (s.next() == s.GT) {
                s.expect(s.GT);
                r = parseExpr1();
                l = new Operation(Operation.Operator.GT, l, r);
            } else if (s.next() == s.GE) {
                s.expect(s.GE);
                r = parseExpr1();
                l = new Operation(Operation.Operator.GE, l, r);
            } else if (s.next() == s.NE) {
                s.expect(s.NE);
                r = parseExpr1();
                l = new Operation(Operation.Operator.NE, l, r);
            } else {
                break;
            }
        }
        return l;
    }

    /**
     * Function from EBNF:
     * expr1 ::= term { ( "+" | "-" ) term }
     * @return Green expression
     */
    private Expression parseExpr1() {
        Expression l = parseTerm();
        while (true) {
            if (s.next() == s.PLUS) {
                s.expect(s.PLUS);
                Expression r = parseTerm();
                l = new Operation(Operation.Operator.ADD, l, r);
            } else if (s.next() == s.MINUS) {
                s.expect(s.MINUS);
                Expression r = parseTerm();
                l = new Operation(Operation.Operator.SUB, l, r);
            } else {
                break;
            }
        }
        return l;
    }

    /**
     * Function from EBNF:
     * term ::= term1 { ( "*" | "/" | "empty" ) term1 }
     * @return Green Expression
     */
    private Expression parseTerm() {
        Expression l = parseTerm1();
        while (true) {
            if (s.next() == s.MUL) {
                s.expect(s.MUL);
                Expression r = parseTerm1();
                l = new Operation(Operation.Operator.MUL, l, r);
            } else if (s.next() == s.DIV) {
                s.expect(s.DIV);
                Expression r = parseTerm1();
                l = new Operation(Operation.Operator.DIV, l, r);
            } else if (s.next() == s.VARIABLE || s.next() == s.LPAREN || s.next() == s.FLOOR) {
                l = parseTerm1();
            } else {
                break;
            }
        }
        return l;
    }

    /**
     * From EBNF:
     * term1 ::= factor { "^" factor }
     * @return Green Expression
     */
    private Expression parseTerm1() {
        Expression l = parseFactor();
        while (true) {
            if (s.next() == s.POW) {
                s.expect(s.POW);
                Expression r = parseFactor();
                l = new Operation(Operation.Operator.POWER, l, r);
            } else {
                break;
            }
        }
        return l;
    }

     /**
     * Function from EBNF:
      * factor ::= integer | variable | floor | "(" expr ")" | "-" expr | "not" expr
     * @return Green Expression
     */
    private Expression parseFactor() {
        Expression l;
        if (s.next() == s.INTEGER) {
            int i = s.expectInteger();
            l = new IntConstant(i);
        } else if (s.next() == s.VARIABLE) {
            String v = s.expectVariable();
            l = new IntVariable(v, Integer.MIN_VALUE, Integer.MAX_VALUE);
        } else if (s.next() == s.FLOOR) {
            s.expect(s.FLOOR);
            l = parseFloor();
        } else if (s.next() == s.LPAREN) {
            s.expect(s.LPAREN);
            l = parseExpr();
            s.expect(s.RPAREN);
        } else if (s.next() == s.MINUS) {
            s.expect(s.MINUS);
            l = parseExpr();
        } else if (s.next() == s.NOT) {
            s.expect(s.NOT);
            l = parseExpr();
            l = new Operation(Operation.Operator.NOT, l);
        } else {
                throw new RuntimeException("expected an expression");
        }

        return l;
    }

    /**
     * From EBNF:
     * floor ::= "floor" "(" expr ")"
     * @return Green Expression
     */
    private Expression parseFloor() {
        Expression l;
        if (s.next() == s.LPAREN) {
            s.expect(s.LPAREN);
            l = parseExpr();
            l = new Operation(Operation.Operator.FLOOR, l);
            s.expect(s.RPAREN);
        } else {
            throw new RuntimeException("expected a left parenthesis");
        }
        return l;
    }
}