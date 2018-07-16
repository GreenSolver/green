package za.ac.sun.cs.green.parser.sexpr;

import za.ac.sun.cs.green.expr.*;

import java.io.ByteArrayInputStream;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.InputMismatchException;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Scanner;

/**
 * @date: 2017/06/26
 * @author: JH Taljaard.
 * Student Number: 18509193.
 * Supervisor: Willem Visser (2018)
 *
 * Description:
 * Most of the code is obtained from Julia, created by Andrea Aquino.
 * The code is adapted to create GREEN expressions.
 */


/**
 * Class to extract boolean expressions over integers from SEXPR data set files.
 */
public class LIAParser {
    /**
     * Returns an integer expression reading it from the given scanner.
     *
     * @param scanner
     *           the scanner from which the expression will be extracted.
     * @return a integer expression extracted from the given scanner.
     */
    private Expression parseIntExpr(Scanner scanner) throws Exception {
        String operator = null;
        try {
            operator = scanner.next();
        } catch (NoSuchElementException e) {
            throw new Exception("Missing operator");
        } catch (IllegalStateException e) {
            throw new Exception("The stream has been closed");
        }

        if (operator.equals("c")) {
            Integer value = null;
            try {
                BigInteger a = scanner.nextBigInteger();
                value = a.intValue();
            } catch (InputMismatchException e) {
                throw new Exception(
                        "An integer value for a constant was expected, but something else was found");
            } catch (NoSuchElementException e) {
                throw new Exception("Missing intenger value for a constant");
            } catch (IllegalStateException e) {
                throw new Exception("The stream has been closed");
            }
            return new IntConstant(value);
        } else if (operator.equals("v")) {
            // Variable?
            Integer value = null;
            try {
                BigInteger a = scanner.nextBigInteger();
                value = a.intValue();
            } catch (InputMismatchException e) {
                throw new Exception(
                        "An integer value as index of a variable was expected, but something else was found");
            } catch (NoSuchElementException e) {
                throw new Exception("Missing index for a variable");
            } catch (IllegalStateException e) {
                throw new Exception("The stream has been closed");
            }

            return new IntVariable("x"+value, Integer.MIN_VALUE+1, Integer.MAX_VALUE-1);
        } else if (operator.equals("+")) {
            Integer arity = null;

            try {
                arity = scanner.nextInt();
            } catch (InputMismatchException e) {
                throw new Exception(
                        "An integer value as the arity of a sum operator was expected, but something else was found");
            } catch (NoSuchElementException e) {
                throw new Exception("Missing arity for sum operator");
            } catch (IllegalStateException e) {
                throw new Exception("The stream has been closed");
            }

            if (arity < 2) {
                throw new Exception("Arity for operator " + operator
                        + " should be at least 2, got " + arity + " instead");
            }

            Operation expr = new Operation(Operation.Operator.ADD,
                    this.parseIntExpr(scanner),
                    this.parseIntExpr(scanner));

            for (int tmp = 2; tmp < arity; tmp++) {
                expr = new Operation(Operation.Operator.ADD,
                        expr,
                        this.parseIntExpr(scanner));
            }

            return expr;
        } else if (operator.equals("*")) {
            Integer arity = null;

            try {
                arity = scanner.nextInt();
            } catch (InputMismatchException e) {
                throw new Exception(
                        "An integer value as the arity of a mul operator was expected, but something else was found");
            } catch (NoSuchElementException e) {
                throw new Exception("Missing arity for mul operator");
            } catch (IllegalStateException e) {
                throw new Exception("The stream has been closed");
            }

            if (arity < 2) {
                throw new Exception("Arity for operator " + operator
                        + " should be at least 2, got " + arity + " instead");
            }

            Operation expr = new Operation(Operation.Operator.MUL,
                    this.parseIntExpr(scanner),
                    this.parseIntExpr(scanner));

            for (int tmp = 2; tmp < arity; tmp++) {
                expr = new Operation(Operation.Operator.MUL,
                        expr,
                        this.parseIntExpr(scanner));
            }

            return expr;
        } else if (operator.equals("-")) {
            Integer arity = null;

            try {
                arity = scanner.nextInt();
            } catch (InputMismatchException e) {
                throw new Exception(
                        "An integer value as the arity of a sub operator was expected, but something else was found");
            } catch (NoSuchElementException e) {
                throw new Exception("Missing arity for sub operator");
            } catch (IllegalStateException e) {
                throw new Exception("The stream has been closed");
            }

            if (arity < 2) {
                throw new Exception("Arity for operator " + operator
                        + " should be at least 2, got " + arity + " instead");
            }

            Operation expr = new Operation(Operation.Operator.SUB,
                    this.parseIntExpr(scanner),
                    this.parseIntExpr(scanner));

            for (int tmp = 2; tmp < arity; tmp++) {
                expr = new Operation(Operation.Operator.SUB,
                        expr,
                        this.parseIntExpr(scanner));
            }

            return expr;
        }
        throw new Exception("Unexpected operator " + operator);
    }

    /**
     * Returns a boolean expression reading it from the given scanner.
     *
     * @param scanner
     *           the scanner from which the expression will be extracted.
     * @return a boolean expression extracted from the given scanner.
     */
    private Operation parseBoolExpr(Scanner scanner) throws Exception {
        List<Operation> clauses = new ArrayList<>();

        Integer nrClauses = null;

        try {
            nrClauses = scanner.nextInt();
        } catch (InputMismatchException e) {
            throw new Exception(
                    "An integer value as the number of clauses of an expression was expected, but something else was found");
        } catch (NoSuchElementException e) {
            throw new Exception("Missing number of clauses of an expression");
        } catch (IllegalStateException e) {
            throw new Exception("The stream has been closed");
        }

        for (int i = 0; i < nrClauses; ++i) {
            List<Operation> inequalities = new ArrayList<>();

            Integer nrIneqs = null;

            try {
                nrIneqs = scanner.nextInt();
            } catch (InputMismatchException e) {
                throw new Exception(
                        "An integer value as the number of inequalities of a clause was expected, but something else was found");
            } catch (NoSuchElementException e) {
                throw new Exception("Missing number of inequalities of a clause");
            } catch (IllegalStateException e) {
                throw new Exception("The stream has been closed");
            }

            for (int j = 0; j < nrIneqs; ++j) {
                Operation inequality = null;

                String comparison = null;
                try {
                    comparison = scanner.next();
                } catch (NoSuchElementException e) {
                    throw new Exception("Missing comparison of an inequality");
                } catch (IllegalStateException e) {
                    throw new Exception("The stream has been closed");
                }

                Expression lhs = this.parseIntExpr(scanner);
                Expression rhs = this.parseIntExpr(scanner);

                switch (comparison) {
                    case "lt":
                        inequality = new Operation(Operation.Operator.LT, lhs, rhs);
                        break;
                    case "le":
                        inequality = new Operation(Operation.Operator.LE, lhs, rhs);
                        break;
                    case "gt":
                        inequality = new Operation(Operation.Operator.GT, lhs, rhs);
                        break;
                    case "ge":
                        inequality = new Operation(Operation.Operator.GE, lhs, rhs);
                        break;
                    case "eq":
                        inequality = new Operation(Operation.Operator.EQ, lhs, rhs);
                        break;
                    case "ne":
                        inequality = new Operation(Operation.Operator.NE, lhs, rhs);
                        break;
                    default:
                        throw new Exception("Unexpected comparison operator " + comparison);
                }

                assert (inequality != null);
                inequalities.add(inequality);
            }

            Operation e = inequalities.get(0);
            for (int j = 1; j < inequalities.size(); j++) {
               e = new Operation(Operation.Operator.OR, e, inequalities.get(j));
            }
            clauses.add(e);
        }

        Operation x = clauses.get(0);
        for (int j = 1; j < clauses.size(); j++) {
            x = new Operation(Operation.Operator.AND, x, clauses.get(j));
        }
        return x;
    }

    /**
     * Returns a boolean expression from the given string.
     *
     * @param s
     *           a string in SEXPR format.
     * @return a boolean expression from the given string.
     */
    public Operation parse(String s) throws Exception {
        return this.parseBoolExpr(new Scanner(new ByteArrayInputStream(s.getBytes())));
    }
}
