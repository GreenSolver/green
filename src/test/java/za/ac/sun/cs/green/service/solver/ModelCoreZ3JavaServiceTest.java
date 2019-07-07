package za.ac.sun.cs.green.service.solver;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.Properties;

import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.service.ModelCoreService;
import za.ac.sun.cs.green.service.ModelCoreService.ModelCore;
import za.ac.sun.cs.green.util.Configuration;

/**
 * JUnit test of ModelCoreZ3JavaServiceTest
 * 
 * @date: 2019/06/06
 * @author: JH Taljaard (USnr 18509193)
 * @contributor: Willem Visser (2018, 2019) (supervisor)
 * @contributor: Jaco Geldenhuys (2017) (supervisor)
 */
public class ModelCoreZ3JavaServiceTest {

	public static Green solver;

	@BeforeClass
	public static void initialize() {
		solver = new Green("GREEN-TEST");
		Properties props = new Properties();
		props.setProperty("green.services", "model");
//        props.setProperty("green.service.model", "(z3bv)");
		props.setProperty("green.service.model", "(bounder z3bv)");
//        props.setProperty("green.service.sat", "(fact (z3bv))");
//        props.setProperty("green.service.sat.fact", "za.ac.sun.cs.green.service.factorizer.ModelFactorizerService");
		props.setProperty("green.service.model.bounder", "za.ac.sun.cs.green.service.bounder.BounderService");
		props.setProperty("green.service.model.z3bv", "za.ac.sun.cs.green.service.z3.ModelCoreZ3JavaService");
		Configuration config = new Configuration(solver, props);
		config.configure();
	}

	@AfterClass
	public static void report() {
		solver.report();
		solver.getStore().flushAll();
	}

	private void checkSat(Expression expression, String expected) {
		Instance i = new Instance(solver, null, expression);
		assertTrue(i != null);
		ModelCore result = (ModelCore) i.request("model");
		assertNotNull(result);
		assertTrue(result.isSat());
		assertEquals(expected, result.getModel().toString());
	}

	private void checkUnsat(Expression expression, String expected) {
		Instance i = new Instance(solver, null, expression);
		assertTrue(i != null);
		ModelCore result = (ModelCore) i.request("model");
		assertNotNull(result);
		assertFalse(result.isSat());
		assertEquals(expected, result.getCore().toString());
	}
	
	@Test
	public void test01() {
		// example: "(aa==0)&&(bb!=1)" => "1*v==0", "1*v+-1!=0" => 0 & 2
		IntVariable v1 = new IntVariable("v0", -10, 99);
		IntConstant c1 = (IntConstant) Operation.ZERO;
		IntVariable v2 = new IntVariable("v1", -10, 99);
		IntConstant c2 = (IntConstant) Operation.ZERO;
		IntConstant c3 = new IntConstant(-1);

		Operation o1 = new Operation(Operation.Operator.EQ, v1, c1);
		Operation o2 = new Operation(Operation.Operator.ADD, v2, c3);
		Operation o3 = new Operation(Operation.Operator.NE, o2, c2);
		Operation o4 = new Operation(Operation.Operator.AND, o1, o3);

		checkSat(o4, "{v0=0, v1=4294967288}");
	}

	@Test
	public void test02() {
		// example: "(aa+bb)<(aa-cc)" => "1*v+1*v+1<=0" => 1
		IntVariable v1 = new IntVariable("v0", -99, 99);
		IntVariable v2 = new IntVariable("v1", -99, 99);
		IntConstant c1 = (IntConstant) Operation.ONE;
		IntConstant c2 = (IntConstant) Operation.ZERO;

		Operation o1 = new Operation(Operation.Operator.ADD, v1, v2);
		Operation o2 = new Operation(Operation.Operator.ADD, o1, c1);
		Operation o3 = new Operation(Operation.Operator.LE, o2, c2);

		checkSat(o3, "{v0=4294967216, v1=66}");
	}

	@Test
	public void test03() {
		// example: "((2+3)*aa)<bb" => 5*0<0
		IntVariable v1 = new IntVariable("aa", -99, 99);
		IntConstant c1 = new IntConstant(5);
		IntVariable v2 = new IntVariable("bb", -99, 99);

		Operation o1 = new Operation(Operation.Operator.MUL, c1, v1);
		Operation o2 = new Operation(Operation.Operator.LT, o1, v2);

		checkSat(o2, "{aa=0, bb=41}");
	}

	@Test
	public void test04() {
		// example: "((2+3)*aa)<bb" => "5*v+-1*v+1<=0" => 5*0 + 0 + 1 < 0
		IntVariable v1 = new IntVariable("v0", 0, 99);
		IntConstant c1 = new IntConstant(5);
		IntVariable v2 = new IntVariable("v1", 0, 99);
		IntConstant c2 = new IntConstant(-1);
		IntConstant c3 = (IntConstant) Operation.ONE;
		IntConstant c4 = (IntConstant) Operation.ZERO;

		Operation o1 = new Operation(Operation.Operator.MUL, c1, v1);
		Operation o2 = new Operation(Operation.Operator.MUL, c2, v2);
		Operation o3 = new Operation(Operation.Operator.ADD, o1, o2);
		Operation o4 = new Operation(Operation.Operator.ADD, o3, c3);
		Operation o5 = new Operation(Operation.Operator.LE, o4, c4);

		checkSat(o5, "{v0=6, v1=32}");
	}

	@Test
	public void test05() {
		// ((x>5)&&(x==(y-1)))&&(y<=7) => -1*v+6<=0, 1*v+-1*v+1==0, 1*v+-7<=0
		IntVariable v1 = new IntVariable("v0", 0, 99);
		IntVariable v2 = new IntVariable("v1", 0, 99);
		IntConstant c0 = new IntConstant(-1);
		IntConstant c1 = new IntConstant(6);
		IntConstant c2 = (IntConstant) Operation.ONE;
		IntConstant c3 = new IntConstant(-7);
		IntConstant c4 = (IntConstant) Operation.ZERO;

		Operation o1 = new Operation(Operation.Operator.MUL, c0, v1);
		Operation o2 = new Operation(Operation.Operator.ADD, o1, c1);
		Operation o3 = new Operation(Operation.Operator.LE, o2, c4);

		Operation o4 = new Operation(Operation.Operator.MUL, c0, v2);
		Operation o5 = new Operation(Operation.Operator.ADD, v1, o4);
		Operation o55 = new Operation(Operation.Operator.ADD, o5, c2);
		Operation o6 = new Operation(Operation.Operator.EQ, o55, c4);

		Operation o7 = new Operation(Operation.Operator.ADD, v2, c3);
		Operation o8 = new Operation(Operation.Operator.LE, o7, c4);

		Operation o9 = new Operation(Operation.Operator.AND, o3, o6);
		Operation o10 = new Operation(Operation.Operator.AND, o9, o8);

		checkSat(o10, "{v0=6, v1=7}");
	}

	@Test
	public void test06() {
		// ((x>5)&&(x==(y-2)))&&(y<=6)
		// UNSAT
		IntVariable v1 = new IntVariable("x", 0, 99);
		IntVariable v2 = new IntVariable("y", 0, 99);
		IntConstant c1 = new IntConstant(5);
		IntConstant c2 = new IntConstant(2);
		IntConstant c3 = new IntConstant(6);

		Operation o1 = new Operation(Operation.Operator.GT, v1, c1);
		Operation o2 = new Operation(Operation.Operator.EQ, v1, new Operation(Operation.Operator.SUB, v2, c2));
		Operation o3 = new Operation(Operation.Operator.LE, v2, c3);

		Operation o4 = new Operation(Operation.Operator.AND, o1, o2);
		Operation o5 = new Operation(Operation.Operator.AND, o4, o3);

		checkUnsat(o5, "false");
	}

	@Test
	public void test07() {
		// ((x>5)&&(x==(y-1)))&&(y<=7)
		IntVariable v1 = new IntVariable("x", 0, 99);
		IntVariable v2 = new IntVariable("y", 0, 99);
		IntConstant c1 = new IntConstant(5);
		IntConstant c2 = new IntConstant(1);
		IntConstant c3 = new IntConstant(7);

		Operation o1 = new Operation(Operation.Operator.GT, v1, c1);
		Operation o2 = new Operation(Operation.Operator.EQ, v1, new Operation(Operation.Operator.SUB, v2, c2));
		Operation o3 = new Operation(Operation.Operator.LE, v2, c3);

		Operation o4 = new Operation(Operation.Operator.AND, o1, o2);
		Operation o5 = new Operation(Operation.Operator.AND, o4, o3);

		checkSat(o5, "{x=6, y=7}");
	}

	@Test
	public void test08() {
		IntVariable v1 = new IntVariable("v", 0, 99);
		IntConstant c1 = new IntConstant(7);

		Operation o1 = new Operation(Operation.Operator.EQ, v1, c1);

		checkSat(o1, "{v=7}");
	}

	@Test
	public void test09() {
		IntVariable v1 = new IntVariable("v", 0, 99);
		IntConstant c1 = new IntConstant(7);

		Operation o1 = new Operation(Operation.Operator.EQ, v1, c1);

		checkSat(o1, "{v=7}");
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
		Operation o6 = new Operation(Operation.Operator.LE, v3, o5);
		Operation o7 = new Operation(Operation.Operator.AND, o4, o6);

		checkSat(o7, "{x=7, y=8, z=6}");
	}

	@Test
	public void test11() {
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

		checkSat(o7, "{x=7, y=8, z=16}");
	}

	@Test
	public void unsatTest01() {
		IntVariable v1 = new IntVariable("x", 0, 99);
		IntConstant c1 = new IntConstant(10);
		Operation o1 = new Operation(Operation.Operator.LT, v1, c1);
		Operation o2 = new Operation(Operation.Operator.GT, v1, c1);

		Operation o4 = new Operation(Operation.Operator.AND, o1, o2);

		checkUnsat(o4, "false");
	}

	@Test
	public void unsatTest02() {
		IntVariable v1 = new IntVariable("x", 0, 99);
		IntConstant c1 = new IntConstant(0);
		Operation o1 = new Operation(Operation.Operator.EQ, v1, c1);
		Operation o2 = new Operation(Operation.Operator.GT, v1, c1);
		Operation o3 = new Operation(Operation.Operator.AND, o1, o2);

		checkUnsat(o3, "false");
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
		checkUnsat(o5, "false");
	}
}
