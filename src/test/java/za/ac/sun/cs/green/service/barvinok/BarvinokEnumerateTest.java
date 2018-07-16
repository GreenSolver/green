package za.ac.sun.cs.green.service.barvinok;

import org.apfloat.Apint;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.util.Configuration;

import java.util.Properties;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

/**
 * @date: 2017/07/26
 * @author: JH Taljaard.
 * Student Number: 18509193.
 * Mentor: Willem Visser
 * Supervisor: Jaco Geldenhuys
 *
 * Description:
 * Test for BarvinokEnumerateService.
 */
public class BarvinokEnumerateTest {
    public static Green solver = null;
    private static final String DEFAULT_BARVENUM_PATH = "lib/barvinok-0.39/barviscc";

    @BeforeClass
    public static void initialize() {
        solver = new Green();
        Properties props = new Properties();

        props.setProperty("green.services", "count");
        props.setProperty("green.service.count", "barvinok");
        props.setProperty("green.service.count.barvinok", "za.ac.sun.cs.green.service.barvinok.BarvinokEnumerateService");

        props.setProperty("green.barvinok.path", DEFAULT_BARVENUM_PATH);
        Configuration config = new Configuration(solver, props);
        config.configure();
    }

    @AfterClass
    public static void report() {
        if (solver != null) {
            solver.report();
        }
    }

    private void check(Expression expression, Expression parentExpression, Apint expected) {
        Instance p = (parentExpression == null) ? null : new Instance(solver, null, parentExpression);
        Instance i = new Instance(solver, p, expression);
        Object result = i.request("count");
        assertNotNull(result);
        assertEquals(Apint.class, result.getClass());
        assertEquals(expected, result);
    }

    private void check(Expression expression, Apint expected) {
        check(expression, null, expected);
    }

    /*
     * Problem
     * 1 * x >= 0
     * 1 * x -10 <= 0
     */
    @Test
    public void test01() {
        IntConstant a = new IntConstant(1);
        IntVariable v = new IntVariable("x", 0, 99);
        Operation t = new Operation(Operation.Operator.MUL, a, v);
        IntConstant c = new IntConstant(0);
        Operation o1 = new Operation(Operation.Operator.GE, t, c);

        IntConstant c1 = new IntConstant(10);
        Operation min = new Operation(Operation.Operator.SUB, t, c1);
        Operation o2 = new Operation(Operation.Operator.LE, min, c);

        Operation o3 = new Operation(Operation.Operator.AND, o1, o2);
        check(o3, new Apint(11));
    }

    /*
     * Problem:
     * P := { [x,y] :
     *          (0 <= x <= 10 and 2*x <= y <= 20 )
     *          and (x=20 and y!=10)
     *          and 5 <= y <= 15};
     */
    @Test
    public void test02() {
        IntConstant zero = new IntConstant(0);
        IntConstant ten = new IntConstant(10);
        IntConstant two = new IntConstant(2);
        IntConstant twenty = new IntConstant(20);
        IntConstant five = new IntConstant(5);
        IntConstant fifteen = new IntConstant(15);

        IntVariable x = new IntVariable("x", 0, 99);
        IntVariable y = new IntVariable("y", 0, 99);

        Operation o1 = new Operation(Operation.Operator.LE, zero, x);
        Operation o2 = new Operation(Operation.Operator.LE, x,ten);
        Operation clause1 = new Operation(Operation.Operator.AND, o1, o2);

        Operation o3 = new Operation(Operation.Operator.MUL, two, x);
        Operation o4 = new Operation(Operation.Operator.LE, o3, y);
        Operation clause2 = new Operation(Operation.Operator.LE, o4, twenty);
        Operation left = new Operation(Operation.Operator.AND, clause1, clause2);
        Operation o6 = new Operation(Operation.Operator.NE, y, ten);
        Operation o7 = new Operation(Operation.Operator.LE, five, y);
        Operation o8 = new Operation(Operation.Operator.LE, y, fifteen);
        Operation right = new Operation(Operation.Operator.AND, o7, o8);

        Operation a = new Operation(Operation.Operator.AND, left, o6);
        Operation b = new Operation(Operation.Operator.AND, a, right);
        check(b, new Apint(57));
    }

    /*
     * Problem:
     * P := { [x,n] : 0 <= x <= n };
     */
    @Test
    public void test03() {
        IntConstant lower1 = new IntConstant(0);
        IntVariable upper1 = new IntVariable("n", 0,99);
        IntVariable v = new IntVariable("x", 0,99);
        Operation o1 = new Operation(Operation.Operator.LE, lower1, v);
        Operation o2 = new Operation(Operation.Operator.LE, v, upper1);
        Operation o3 = new Operation(Operation.Operator.AND, o1, o2);

        check(o3, new Apint(5050));
    }

    /*
     * Problem:
     * P := [n,m] -> { [i,j] : 0 <= x <= n and x <= y <= m };
     */
    @Test
    public void test04() {
        IntConstant lower1 = new IntConstant(0);
        IntVariable upper1 = new IntVariable("n", 0,99);

        IntVariable v1 = new IntVariable("x", 0,99);
        Operation o1 = new Operation(Operation.Operator.LE, lower1, v1);
        Operation o2 = new Operation(Operation.Operator.LE, v1, upper1);
        Operation o3 = new Operation(Operation.Operator.AND, o1, o2);

        IntVariable lower2 = v1;
        IntVariable v2 = new IntVariable("y", 0,99);
        IntVariable upper2 = new IntVariable("m", 0,99);
        Operation o4 = new Operation(Operation.Operator.LE, lower2, v2);
        Operation o5 = new Operation(Operation.Operator.LE, v2, upper2);
        Operation o6 = new Operation(Operation.Operator.AND, o4, o5);

        Operation o7 = new Operation(Operation.Operator.AND, o3, o6);
        Operation o8 = new Operation(Operation.Operator.EQ, upper1, new IntConstant(10));
        Operation o9 = new Operation(Operation.Operator.AND, o7, o8);

        Operation o10 = new Operation(Operation.Operator.EQ, upper2, new IntConstant(10));
        Operation o11 = new Operation(Operation.Operator.AND, o9, o10);

        check(o11, new Apint(66));
    }

    /*
     * Problem:
     * x > y and
     * 0 <= x <= 99 && 0 <= x <= 99
     */
    @Test
    public void test05() {
        IntVariable v1 = new IntVariable("x", 0, 99);
        IntVariable v2 = new IntVariable("y", 0, 99);

        Operation o1 = new Operation(Operation.Operator.GT, v1, v2);
        check(o1, new Apint(4950));
    }

    /*
     * Problem:
     * x > y and
     * 0 <= x <= 9 && 0 <= x <= 9
     */
    @Test
    public void test06() {
        IntVariable v1 = new IntVariable("x", 0, 9);
        IntVariable v2 = new IntVariable("y", 0, 9);

        Operation o1 = new Operation(Operation.Operator.GT, v1, v2);
        check(o1, new Apint(45));
    }

    /**
     * Basic test.
     * Problem:
     *   1 * aa == 0
     * Count:
     *   1
     */
    @Test
    public void test07() {
        IntConstant a = new IntConstant(1);
        IntVariable v = new IntVariable("aa", 0, 99);
        IntConstant c = new IntConstant(0);

        Operation t = new Operation(Operation.Operator.MUL, a, v);
        Operation o = new Operation(Operation.Operator.EQ, t, c);
        check(o, new Apint(1));
    }

    /*
     * Problem:
     * P := [n] -> { [x] : 0 <= x <= n };
     */
    @Test
    public void test08() {
        int n = 9;

        IntConstant lower1 = new IntConstant(0);
        IntConstant upper1 = new IntConstant(n);
        IntVariable v = new IntVariable("x", 0,99);

        Operation o1 = new Operation(Operation.Operator.LE, lower1, v);
        Operation o2 = new Operation(Operation.Operator.LE, v, upper1);
        Operation o3 = new Operation(Operation.Operator.AND, o1, o2);

        check(o3, new Apint(n+1));
    }
}
