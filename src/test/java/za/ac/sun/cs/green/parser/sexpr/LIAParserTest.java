package za.ac.sun.cs.green.parser.sexpr;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;
import org.junit.Test;
import static org.junit.Assert.assertTrue;

/**
 * @date: 2017/06/26
 * @author: JH Taljaard.
 * Student Number: 18509193.
 * Supervisor: Jaco Geldenhuys  (2017)
 * Mentor:      Willem Visser   (2017)
 *
 * Description:
 * JUnit test for testing the LIA parser.
 */
public class LIAParserTest {
    public static Green solver;

    private void finalCheck(Expression expression, String expected) {
        assertTrue(((expression.toString()).equals(expected)));
    }

    private void check(String input, String expected) {
        LIAParser parser = new LIAParser();
        Operation o = null;

        try {
            o = parser.parse(input);
        } catch (Exception e) {
            e.printStackTrace();
        }

        finalCheck(o, expected);
    }

    @Test
    public void test01() {
        String s1 = "1 1 lt v 0 c 0";
        String v1 = "x0<0";

        check(s1, v1);
    }

    @Test
    public void test02() {
        String s1 = "1 1 le v 0 c 0";
        String v1 = "x0<=0";

        check(s1, v1);
    }

    @Test
    public void test03() {
        String s1 = "1 1 gt v 0 c 0";
        String v1 = "x0>0";

        check(s1, v1);
    }

    @Test
    public void test04() {
        String s1 = "1 1 ge v 0 c 0";
        String v1 = "x0>=0";

        check(s1, v1);
    }

    @Test
    public void test05() {
        String s1 = "1 1 eq v 0 c 0";
        String v1 = "x0==0";
        check(s1, v1);
    }

    @Test
    public void test06() {
        String s1 = "1 1 ne v 0 c 0";
        String v1 = "x0!=0";

        check(s1, v1);
    }

    @Test
    public void test07() {
        String s1 = "1 1 ne * 2 v 0 v 0 c 0";
        String v1 = "(x0*x0)!=0";

        check(s1, v1);
    }

    @Test
    public void test08() {
        String s1 = "1 1 ne * 2 + 2 v 1 c 5 + 2 v 0 c 10 + 2 * 2 v 1 c 5 * 2 v 0 c 10";
        String v1 = "((x1+5)*(x0+10))!=((x1*5)+(x0*10))";

        check(s1, v1);
    }

    @Test
    public void test09() {
        String s1 = "1 1 ne * 3 v 0 v 1 v 2 v 3";
        String v1 = "((x0*x1)*x2)!=x3";

        check(s1, v1);
    }

    @Test
    public void test10() {
        String s1 = "2 2 lt v 0 c 0 lt v 0 c 1 1 gt v 0 c 0";
        String v1 = "((x0<0)||(x0<1))&&(x0>0)";

        check(s1, v1);
    }
}
