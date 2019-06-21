package za.ac.sun.cs.green.service.solver;

import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.*;
import za.ac.sun.cs.green.service.ModelCoreService;
import za.ac.sun.cs.green.util.Configuration;

import java.util.Properties;

import static org.junit.Assert.assertTrue;

/**
 * @date: 2019/06/06
 * @author: JH Taljaard.
 * Student Number: 18509193.
 * Supervisor:  Willem Visser (2018,2019),
 *              Jaco Geldenhuys (2017)
 *
 * Description:
 * JUnit test of ModelZ3JavaBVServiceTest
 */
public class ModelZ3JavaBVServiceTest {

    public static Green solver;
    private final static int SIZE64 = 64;
    private final static int SIZE32 = 32;

    @BeforeClass
    public static void initialize() {
        solver = new Green();
        Properties props = new Properties();
        props.setProperty("green.services", "model");
//        props.setProperty("green.service.model", "(z3bv)");
        props.setProperty("green.service.model", "(bounder (z3bv))");
//        props.setProperty("green.service.sat", "(fact (z3bv))");
//        props.setProperty("green.service.sat.fact", "za.ac.sun.cs.green.service.factorizer.ModelFactorizerService");
        props.setProperty("green.service.model.bounder", "za.ac.sun.cs.green.service.bounder.BounderService");
        props.setProperty("green.service.model.z3bv", "za.ac.sun.cs.green.service.z3.ModelZ3JavaBVService");
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
        assertTrue(i != null);
        Object result = i.request("model");
        if (result == null) {
            result = false;
        }
        System.out.println(result);
        assertTrue(((result.toString()).equals(expected)));
    }

    @Test
    public void test01() {
        // example: "(aa==0)&&(bb!=1)" => "1*v==0", "1*v+-1!=0" => 0 & 2
        IntegerVariable v1 = new IntegerVariable("v0", -10,99, 32);
        IntegerConstant c1 = (IntegerConstant) IntegerConstant.ZERO32;
        IntegerVariable v2 = new IntegerVariable("v1", -10, 99, 32);
        IntegerConstant c2 = (IntegerConstant) IntegerConstant.ZERO32;
        IntegerConstant c3 = new IntegerConstant(-1, 32);

        Operation o1 = new Operation(Operation.Operator.EQ, v1, c1);
        Operation o2 = new Operation(Operation.Operator.ADD, v2, c3);
        Operation o3 = new Operation(Operation.Operator.NE, o2, c2);
        Operation o4 = new Operation(Operation.Operator.AND, o1, o3);

        check(o4, "{v0=0, v1=4294967288}");
    }

    @Test
    public void test02() {
        // example: "(aa+bb)<(aa-cc)" => "1*v+1*v+1<=0" => 1
        IntegerVariable v1 = new IntegerVariable("v0", -99,99, 32);
        IntegerVariable v2 = new IntegerVariable("v1", -99, 99, 32);
        IntegerConstant c1 = (IntegerConstant) IntegerConstant.ONE32;
        IntegerConstant c2 = (IntegerConstant) IntegerConstant.ZERO32;

        Operation o1 = new Operation(Operation.Operator.ADD, v1, v2);
        Operation o2 = new Operation(Operation.Operator.ADD, o1, c1);
        Operation o3 = new Operation(Operation.Operator.LE, o2, c2);

        check(o3, "{v0=4294967268, v1=4294967272}");
    }

    @Test
    public void test03() {
        // example: "((2+3)*aa)<bb" =>  5*0<0
        IntegerVariable v1 = new IntegerVariable("aa", -99,99, 32);
        IntegerConstant c1 = new IntegerConstant(5, 32);
        IntegerVariable v2 = new IntegerVariable("bb", -99, 99, 32);

        Operation o1 = new Operation(Operation.Operator.MUL, c1, v1);
        Operation o2 = new Operation(Operation.Operator.LT, o1, v2);

        check(o2, "{aa=4294967280, bb=4294967284}");
    }

    @Test
    public void test04() {
        // example: "((2+3)*aa)<bb" => "5*v+-1*v+1<=0" => 5*0 + 0 + 1 < 0
        IntegerVariable v1 = new IntegerVariable("v0", 0,99,32);
        IntegerConstant c1 = new IntegerConstant(5, 32);
        IntegerVariable v2 = new IntegerVariable("v1", 0, 99,32);
        IntegerConstant c2 = new IntegerConstant(-1, 32);
        IntegerConstant c3 = (IntegerConstant) IntegerConstant.ONE32;
        IntegerConstant c4 = (IntegerConstant) IntegerConstant.ZERO32;

        Operation o1 = new Operation(Operation.Operator.MUL, c1, v1);
        Operation o2 = new Operation(Operation.Operator.MUL, c2, v2);
        Operation o3 = new Operation(Operation.Operator.ADD, o1, o2);
        Operation o4 = new Operation(Operation.Operator.ADD, o3, c3);
        Operation o5 = new Operation(Operation.Operator.LE, o4, c4);

        check(o5, "{v0=0, v1=58}");
    }

    @Test
    public void test05() {
        //((x>5)&&(x==(y-1)))&&(y<=7) => -1*v+6<=0, 1*v+-1*v+1==0, 1*v+-7<=0
        int size = 64;
        IntegerVariable v1 = new IntegerVariable("v0", 0,99,size);
        IntegerVariable v2 = new IntegerVariable("v1",0,99,size);
        IntegerConstant c0 = new IntegerConstant(-1,size);
        IntegerConstant c1 = new IntegerConstant(6,size);
        IntegerConstant c2 = (IntegerConstant) IntegerConstant.ONE64;
        IntegerConstant c3 = new IntegerConstant(-7,size);
        IntegerConstant c4 = (IntegerConstant) IntegerConstant.ZERO64;

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

        check(o10, "{v0=6, v1=7}");
    }

    @Test
    public void test06() {
        // ((x>5)&&(x==(y-2)))&&(y<=6)
        // UNSAT
        IntegerVariable v1 = new IntegerVariable("x", 0,99, SIZE32);
        IntegerVariable v2 = new IntegerVariable("y",0 ,99, SIZE32);
        IntegerConstant c1 = new IntegerConstant(5, SIZE32);
        IntegerConstant c2 = new IntegerConstant(2, SIZE32);
        IntegerConstant c3 = new IntegerConstant(6, SIZE32);

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
        int size = 64;
        IntegerVariable v1 = new IntegerVariable("x", 0,99, size);
        IntegerVariable v2 = new IntegerVariable("y",0 ,99, size);
        IntegerConstant c1 = new IntegerConstant(5, size);
        IntegerConstant c2 = new IntegerConstant(1, size);
        IntegerConstant c3 = new IntegerConstant(7, size);

        Operation o1 = new Operation(Operation.Operator.GT, v1, c1);
        Operation o2 = new Operation(Operation.Operator.EQ, v1, new Operation(Operation.Operator.SUB, v2, c2));
        Operation o3 = new Operation(Operation.Operator.LE, v2, c3);

        Operation o4 = new Operation(Operation.Operator.AND, o1, o2);
        Operation o5 = new Operation(Operation.Operator.AND, o4, o3);

        check(o5, "{x=6, y=7}");
    }

    @Test
    public void test08() {
        IntegerVariable v1 = new IntegerVariable("v", 0, 99,SIZE32);
        IntegerConstant c1 = new IntegerConstant(7,SIZE32);

        Operation o1 = new Operation(Operation.Operator.EQ, v1, c1);

        check(o1, "{v=7}");
    }

    @Test
    public void test09() {
        IntegerVariable v1 = new IntegerVariable("v", 0, 99,64);
        IntegerConstant c1 = new IntegerConstant(7,64);

        Operation o1 = new Operation(Operation.Operator.EQ, v1, c1);

        check(o1, "{v=7}");
    }

    @Test
    public void test10() {
        // x = 7 & y = x + 1 & z <= y+9
        int size = 64;
        IntegerVariable v1 = new IntegerVariable("x", 0, 99, size);
        IntegerVariable v2 = new IntegerVariable("y", 0, 99, size);
        IntegerVariable v3 = new IntegerVariable("z", 0, 99, size);
        IntegerConstant c1 = new IntegerConstant(7, size);
        IntegerConstant c2 = new IntegerConstant(1, size);
        IntegerConstant c3 = new IntegerConstant(9, size);

        Operation o1 = new Operation(Operation.Operator.EQ, v1, c1);
        Operation o2 = new Operation(Operation.Operator.ADD, v1, c2);
        Operation o3 = new Operation(Operation.Operator.EQ, v2, o2);

        Operation o4 = new Operation(Operation.Operator.AND, o1, o3);
        Operation o5 = new Operation(Operation.Operator.ADD, v2, c3);
        Operation o6 = new Operation(Operation.Operator.LE, v3, o5);
        Operation o7 = new Operation(Operation.Operator.AND, o4, o6);

        check(o7, "{x=7, y=8, z=4}");
    }

    @Test
    public void test11() {
        // x = 7 & y = x + 1 & z <= y+9
        int size = 64;
        IntegerVariable v1 = new IntegerVariable("x", 0, 99, size);
        IntegerVariable v2 = new IntegerVariable("y", 0, 99, size);
        IntegerVariable v3 = new IntegerVariable("z", 0, 99, size);
        IntegerConstant c1 = new IntegerConstant(7, size);
        IntegerConstant c2 = new IntegerConstant(1, size);
        IntegerConstant c3 = new IntegerConstant(9, size);

        Operation o1 = new Operation(Operation.Operator.EQ, v1, c1);
        Operation o2 = new Operation(Operation.Operator.ADD, v1, c2);
        Operation o3 = new Operation(Operation.Operator.EQ, v2, o2);
        Operation o4 = new Operation(Operation.Operator.AND, o1, o3);

        Operation o5 = new Operation(Operation.Operator.ADD, v2, c3);
        Operation o6 = new Operation(Operation.Operator.LT, v3, o5);
        Operation o7 = new Operation(Operation.Operator.AND, o4, o6);

        check(o7, "{x=7, y=8, z=16}");
    }

    @Test
    public void unsatTest01() {
        IntegerVariable v1 = new IntegerVariable("x", 0, 99, SIZE32);
        IntegerConstant c1 = new IntegerConstant(10, SIZE32);
        Operation o1 = new Operation(Operation.Operator.LT, v1, c1);
        Operation o2 = new Operation(Operation.Operator.GT, v1, c1);

        Operation o4 = new Operation(Operation.Operator.AND, o1, o2);

        check(o4, "false");
    }

    @Test
    public void unsatTest02() {
        int size = 64;
        IntegerVariable v1 = new IntegerVariable("x", 0, 99, size);
        IntegerConstant c1 = new IntegerConstant(0, size);
        Operation o1 = new Operation(Operation.Operator.EQ, v1, c1);
        Operation o2 = new Operation(Operation.Operator.GT, v1, c1);
        Operation o3 = new Operation(Operation.Operator.AND, o1, o2);

        check(o3, "false");
    }

    @Test
    public void unsatTest03() {
        IntegerVariable v1 = new IntegerVariable("x", 0, 99, SIZE32);
        IntegerConstant c1 = new IntegerConstant(0, SIZE32);
        Operation o1 = new Operation(Operation.Operator.EQ, v1, c1);
        Operation o2 = new Operation(Operation.Operator.LT, v1, c1);
        Operation o3 = new Operation(Operation.Operator.GT, v1, c1);
        Operation o4 = new Operation(Operation.Operator.AND, o1, o2);
        Operation o5 = new Operation(Operation.Operator.AND, o4, o3);
        check(o5, "false");
    }
}
