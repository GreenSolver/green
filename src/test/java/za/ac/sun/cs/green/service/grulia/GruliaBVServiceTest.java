package za.ac.sun.cs.green.service.grulia;

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

import static org.junit.Assert.assertTrue;

/**
 * @date: 2018/08/23
 * @author: JH Taljaard.
 * Student Number: 18509193.
 * Supervisor:  Willem Visser (2018,2019),
 *              Jaco Geldenhuys (2017)
 *
 * Description:
 * JUnit test of Grulia
 */
public class GruliaBVServiceTest {

    public static Green solver;

    @BeforeClass
    public static void initialize() {
        solver = new Green();
        Properties props = new Properties();
        props.setProperty("green.services", "sat");
        props.setProperty("green.service.sat", "(grulia)");
        props.setProperty("green.service.sat.grulia", "za.ac.sun.cs.green.service.grulia.GruliaBVService");
        Configuration config = new Configuration(solver, props);
        config.configure();
    }

    @AfterClass
    public static void report() {
        solver.report();
        solver.getStore().flushAll();
    }

    private void check(Expression expression, String expected) {
        Instance i = new Instance(solver, null, expression);
        Object result = i.request("sat");
        assertTrue(((result.toString()).equals(expected)));
    }

    @Test
    public void test01() {
        // example: "(aa==0)&&(bb!=1)" => "1*v==0", "1*v+-1!=0" => 0 & 2
        // SAT-Delta: 2 (for reference model 0)
        IntVariable v1 = new IntVariable("v0", -10,99);
        IntConstant c1 = new IntConstant(0);
        IntVariable v2 = new IntVariable("v1", -10, 99);
        IntConstant c2 = new IntConstant(0);
        IntConstant c3 = new IntConstant(-1);

        Operation o1 = new Operation(Operation.Operator.EQ, v1, c1);
        Operation o2 = new Operation(Operation.Operator.ADD, v2, c3);
        Operation o3 = new Operation(Operation.Operator.NE, o2, c2);
        Operation o4 = new Operation(Operation.Operator.AND, o1, o3);

        check(o4, "true");
    }

    @Test
    public void test02() {
        // example: "(aa+bb)<(aa-cc)" => "1*v+1*v+1<=0" => 1
        // SAT-Delta: 1 (for reference model 0)
        IntVariable v1 = new IntVariable("v0", -99,99);
        IntVariable v2 = new IntVariable("v1", -99, 99);
        IntConstant c1 = new IntConstant(1);
        IntConstant c2 = new IntConstant(0);

        Operation o1 = new Operation(Operation.Operator.ADD, v1, v2);
        Operation o2 = new Operation(Operation.Operator.ADD, o1, c1);
        Operation o3 = new Operation(Operation.Operator.LE, o2, c2);

        check(o3, "true");
    }

    @Test
    public void test03() {
        // example: "((2+3)*aa)<bb" =>  5*0<0
        // SAT-Delta: 1 (for reference model 0)
        IntVariable v1 = new IntVariable("aa", -99,99);
        IntConstant c1 = new IntConstant(5);
        IntVariable v2 = new IntVariable("bb", -99, 99);

        Operation o1 = new Operation(Operation.Operator.MUL, c1, v1);
        Operation o2 = new Operation(Operation.Operator.LT, o1, v2);

        check(o2, "true");
    }

    @Test
    public void test04() {
        // example: "((2+3)*aa)<bb" => "5*v+-1*v+1<=0" => 5*0 + 0 + 1 < 0
        // SAT-Delta: 1 (for reference model 0)
        IntVariable v1 = new IntVariable("v0", 0,99);
        IntConstant c1 = new IntConstant(5);
        IntVariable v2 = new IntVariable("v1", 0, 99);
        IntConstant c2 = new IntConstant(-1);
        IntConstant c3 = new IntConstant(1);
        IntConstant c4 = new IntConstant(0);

        Operation o1 = new Operation(Operation.Operator.MUL, c1, v1);
        Operation o2 = new Operation(Operation.Operator.MUL, c2, v2);
        Operation o3 = new Operation(Operation.Operator.ADD, o1, o2);
        Operation o4 = new Operation(Operation.Operator.ADD, o3, c3);
        Operation o5 = new Operation(Operation.Operator.LE, o4, c4);

        check(o5, "true");
    }

    @Test
    public void test05() {
        //((x>5)&&(x==(y-1)))&&(y<=7) => -1*v+6<=0, 1*v+-1*v+1==0, 1*v+-7<=0
        // => 0+6 <= 0 + 0 - 0 + 1 == 0 + 0 - 7 <= 0
        // => 6 + 1 + 7 = 14
        // SAT-Delta: 14 (for reference model 0)
        IntVariable v1 = new IntVariable("v0", 0,99);
        IntVariable v2 = new IntVariable("v1",0,99);
        IntConstant c0 = new IntConstant(-1);
        IntConstant c1 = new IntConstant(6);
        IntConstant c2 = new IntConstant(1);
        IntConstant c3 = new IntConstant(-7);
        IntConstant c4 = new IntConstant(0);

        Operation o1 = new Operation(Operation.Operator.MUL, c0, v1);
        Operation o2 = new Operation(Operation.Operator.ADD, o1, c1);
        Operation o3 = new Operation(Operation.Operator.LE, o2, c4);

        Operation o4 = new Operation(Operation.Operator.MUL, c0, v2);
        Operation o5 = new Operation(Operation.Operator.ADD, v1, o4);
        Operation o_ = new Operation(Operation.Operator.ADD, o5, c2);
        Operation o6 = new Operation(Operation.Operator.EQ, o_, c4);

        Operation o7 = new Operation(Operation.Operator.ADD, v2, c3);
        Operation o8 = new Operation(Operation.Operator.LE, o7, c4);

        Operation o9 = new Operation(Operation.Operator.AND, o3, o6);
        Operation o10 = new Operation(Operation.Operator.AND, o9, o8);

        check(o10, "true");
    }

    @Test
    public void test06() {
        // ((x>5)&&(x==(y-2)))&&(y<=6)
        // UNSAT
        // SAT-Delta: 14 (for reference model 0)
        IntVariable v1 = new IntVariable("x", 0,99);
        IntVariable v2 = new IntVariable("y",0 ,99);
        IntConstant c1 = new IntConstant(5);
        IntConstant c2 = new IntConstant(2);
        IntConstant c3 = new IntConstant(6);

        Operation o1 = new Operation(Operation.Operator.GT, v1, c1);
        Operation o2 = new Operation(Operation.Operator.EQ, v1, new Operation(Operation.Operator.SUB, v2, c2));
        Operation o3 = new Operation(Operation.Operator.LE, v2, c3);

        Operation o4 = new Operation(Operation.Operator.AND, o1, o2);
        Operation o5 = new Operation(Operation.Operator.AND, o4, o3);

        check(o5, "false");
    }

    @Test
    public void test07() {
        // ((x>5)&&(x==(y-1)))&&(y<=7)
        // SAT-Delta: 14 (for reference model 0)
        IntVariable v1 = new IntVariable("x", 0,99);
        IntVariable v2 = new IntVariable("y",0 ,99);
        IntConstant c1 = new IntConstant(5);
        IntConstant c2 = new IntConstant(1);
        IntConstant c3 = new IntConstant(7);

        Operation o1 = new Operation(Operation.Operator.GT, v1, c1);
        Operation o2 = new Operation(Operation.Operator.EQ, v1, new Operation(Operation.Operator.SUB, v2, c2));
        Operation o3 = new Operation(Operation.Operator.LE, v2, c3);

        Operation o4 = new Operation(Operation.Operator.AND, o1, o2);
        Operation o5 = new Operation(Operation.Operator.AND, o4, o3);

        check(o5, "true");
    }

    @Test
    public void test08() {
        IntVariable v1 = new IntVariable("v", 0, 99);
        IntConstant c1 = new IntConstant(7);

        Operation o1 = new Operation(Operation.Operator.EQ, v1, c1);

        check(o1, "true");
    }

    @Test
    public void test09() {
        // x = 7 & y = x + 1 & z <= y+9
        IntVariable v1 = new IntVariable("x", 0, 99);
        IntVariable v2 = new IntVariable("y", 0, 99);
        IntVariable v3 = new IntVariable("z", 0, 99);
        IntConstant c1 = new IntConstant(7);
        IntConstant c2 = new IntConstant(1);
        IntConstant c3 = new IntConstant(9);

        Operation o1 = new Operation(Operation.Operator.EQ, v1, c1);
        Operation o2 = new Operation(Operation.Operator.ADD, v1, c2);
        Operation o3 = new Operation(Operation.Operator.EQ, v2, o2);

        Operation o4 = new Operation(Operation.Operator.AND, o1, o3);
        Operation o5 = new Operation(Operation.Operator.ADD, v2, c3);
        Operation o6 = new Operation(Operation.Operator.LE, v3, o5);
        Operation o7 = new Operation(Operation.Operator.AND, o4, o6);

        check(o7, "true");
    }

    @Test
    public void test10() {
        // x = 7 & y = x + 1 & z <= y+9
        IntVariable v1 = new IntVariable("x", 0, 99);
        IntVariable v2 = new IntVariable("y", 0, 99);
        IntVariable v3 = new IntVariable("z", 0, 99);
        IntConstant c1 = new IntConstant(7);
        IntConstant c2 = new IntConstant(1);
        IntConstant c3 = new IntConstant(9);

        Operation o1 = new Operation(Operation.Operator.EQ, v1, c1);
        Operation o2 = new Operation(Operation.Operator.ADD, v1, c2);
        Operation o3 = new Operation(Operation.Operator.EQ, v2, o2);
        Operation o4 = new Operation(Operation.Operator.AND, o1, o3);

        Operation o5 = new Operation(Operation.Operator.ADD, v2, c3);
        Operation o6 = new Operation(Operation.Operator.LT, v3, o5);
        Operation o7 = new Operation(Operation.Operator.AND, o4, o6);

        check(o7, "true");
    }

    @Test
    public void test11() {
        int min = -100;
        int max = 1000;
        IntConstant const32768 = new IntConstant(-32768);
        IntConstant const0 = new IntConstant(0);
        IntConstant const8 = new IntConstant(8);
        IntConstant const16 = new IntConstant(16);
        IntConstant const48 = new IntConstant(48);
        IntConstant const65536 = new IntConstant(65536);
        IntVariable a1 = new IntVariable("a1", min, max);
        IntVariable c2 = new IntVariable("c2", min, max);

        Operation o1 = new Operation(Operation.Operator.LE, c2, const65536);
        Operation o2 = new Operation(Operation.Operator.GE, c2, const32768);
        Operation o3 = new Operation(Operation.Operator.AND, o1, o2);

        Operation o4 = new Operation(Operation.Operator.MUL, a1, const8);
        Operation o40 = new Operation(Operation.Operator.SUB, const48, o4);
        Operation o400 = new Operation(Operation.Operator.MOD, o40, const16);
        Operation o5 = new Operation(Operation.Operator.NE, o400, const0);

        Operation o6 = new Operation(Operation.Operator.AND, o5, o3);
        check(o6, "true");
    }

    @Test
    public void unsatTest01() {
        IntVariable v1 = new IntVariable("x", 0, 99);
        IntConstant c1 = new IntConstant(10);
        Operation o1 = new Operation(Operation.Operator.LT, v1, c1);
        Operation o2 = new Operation(Operation.Operator.GT, v1, c1);

        Operation o4 = new Operation(Operation.Operator.AND, o1, o2);

        check(o4, "false");
    }

    @Test
    public void unsatTest02() {
        IntVariable v1 = new IntVariable("x", 0, 99);
        IntConstant c1 = new IntConstant(0);
        Operation o1 = new Operation(Operation.Operator.EQ, v1, c1);
        Operation o2 = new Operation(Operation.Operator.GT, v1, c1);
        Operation o3 = new Operation(Operation.Operator.AND, o1, o2);

        check(o3, "false");
    }

    @Test
    public void unsatTest03() {
        IntVariable v1 = new IntVariable("x", 0, 99);
        IntConstant c1 = new IntConstant(0);
        Operation o1 = new Operation(Operation.Operator.EQ, v1, c1);
        Operation o2 = new Operation(Operation.Operator.LT, v1, c1);
        Operation o3 = new Operation(Operation.Operator.GT, v1, c1);
        Operation o4 = new Operation(Operation.Operator.AND, o1, o2);
        Operation o5 = new Operation(Operation.Operator.AND, o4, o3);

        check(o5, "false");
    }
}

