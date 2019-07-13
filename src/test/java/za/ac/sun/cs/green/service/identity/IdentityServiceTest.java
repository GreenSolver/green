package za.ac.sun.cs.green.service.identity;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.Properties;

import org.junit.BeforeClass;
import org.junit.Test;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.util.Configuration;

/**
 * Tests for {@link za.ac.sun.cs.green.service.identity.IdentityService}
 */
public class IdentityServiceTest {

	/**
	 * Green server without the identity service.
	 */
	public static Green solver0;

	/**
	 * Green server with the identity service.
	 */
	public static Green solver1;
	
	/**
	 * Create and configure the two Green solvers, one with and one without the identity service.
	 */
	@BeforeClass
	public static void initialize() {
		solver0 = new Green("GREEN-TEST");
		Properties props = new Properties();
		props.setProperty("green.services", "idtest");
		props.setProperty("green.service.idtest", "(choco)");
		props.setProperty("green.service.idtest.choco", "za.ac.sun.cs.green.service.choco4.SATChocoService");
		new Configuration(solver0, props).configure();
		
		solver1 = new Green("GREEN-TEST");
		props.setProperty("green.service.idtest", "(identity choco)");
		props.setProperty("green.service.idtest.identity", "za.ac.sun.cs.green.service.identity.IdentityService");
		new Configuration(solver1, props).configure();
	}

	/**
	 * Check that satisfiability of the expression with and without the identity service and check that these two results are the same.
	 *
	 * @param expression expression to check
	 * @param result expected result
	 */
	private void check(Expression expression, boolean result) {
		Object result0 = new Instance(solver0, null, expression).request("idtest");
		assertTrue(result0 instanceof Boolean);
		Object result1 = new Instance(solver1, null, expression).request("idtest");
		assertTrue(result1 instanceof Boolean);
		assertEquals(result, result0);
		assertEquals(result, result1);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v in [0, 99]) && (v == 0)
	 * </pre>
	 *
	 * @result both solver should report that the expression is satisfiable
	 */
	@Test
	public void test01() {
		IntVariable v = new IntVariable("v", 0, 99);
		IntConstant c = new IntConstant(0);
		Operation o = new Operation(Operation.Operator.EQ, v, c);
		check(o, true);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v1 in [0, 99]) && (v2 in [0, 99]) && (v1 == 0) && (v2 == 0)
	 * </pre>
	 *
	 * @result both solver should report that the expression is satisfiable
	 */
	@Test
	public void test02() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntVariable v2 = new IntVariable("v2", 0, 99);
		IntConstant c1 = new IntConstant(0);
		IntConstant c2 = new IntConstant(0);
		Operation o1 = new Operation(Operation.Operator.EQ, v1, c1);
		Operation o2 = new Operation(Operation.Operator.EQ, v2, c2);
		Operation o = new Operation(Operation.Operator.AND, o1, o2);
		check(o, true);
	}
	
	/**
	 * Test:
	 * 
	 * <pre>
	 * (2 == 2)
	 * </pre>
	 *
	 * @result both solver should report that the expression is satisfiable
	 */
	@Test
	public void test03() {
		IntConstant c1 = new IntConstant(2);
		IntConstant c2 = new IntConstant(2);
		Operation o = new Operation(Operation.Operator.EQ, c1, c2);
		check(o, true);
	}
	
	/**
	 * Test:
	 * 
	 * <pre>
	 * (2 == 3)
	 * </pre>
	 *
	 * @result both solver should report that the expression is unsatisfiable
	 */
	@Test
	public void test04() {
		IntConstant c1 = new IntConstant(2);
		IntConstant c2 = new IntConstant(3);
		Operation o = new Operation(Operation.Operator.EQ, c1, c2);
		check(o, false);
	}
	
	/**
	 * Test:
	 * 
	 * <pre>
	 * (v1 in [0, 99]) && (v2 in [9, 99]) && (v1 == 0) && (v2 == 0)
	 * </pre>
	 *
	 * @result both solver should report that the expression is unsatisfiable
	 */
	@Test
	public void test05() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntVariable v2 = new IntVariable("v2", 9, 99);
		IntConstant c1 = new IntConstant(0);
		IntConstant c2 = new IntConstant(0);
		Operation o1 = new Operation(Operation.Operator.EQ, v1, c1);
		Operation o2 = new Operation(Operation.Operator.EQ, v2, c2);
		Operation o = new Operation(Operation.Operator.AND, o1, o2);
		check(o, false);
	}
	
}

/*
 * 
 * @Test public void test02b() { IntConstant c1 = new IntConstant(2);
 * IntConstant c2 = new IntConstant(2); Operation o = new
 * Operation(Operation.Operator.LT, c1, c2); check(o, "2<2", "2<2"); }
 * 
 * @Test public void test03() { IntVariable v1 = new IntVariable("v1", 0, 99);
 * IntConstant c1 = new IntConstant(0); Operation o1 = new
 * Operation(Operation.Operator.EQ, v1, c1); IntVariable v2 = new
 * IntVariable("v2", 0, 99); IntConstant c2 = new IntConstant(1); Operation o2 =
 * new Operation(Operation.Operator.NE, v2, c2); check(o1, o2,
 * "(v1==0)&&(v2!=1)", "v1==0"); }
 * 
 * @Test public void test04() { IntVariable v1 = new IntVariable("v1", 0, 99);
 * IntConstant c1 = new IntConstant(0); Operation o1 = new
 * Operation(Operation.Operator.EQ, v1, c1); IntVariable v2 = new
 * IntVariable("v2", 0, 99); IntConstant c2 = new IntConstant(1); Operation o2 =
 * new Operation(Operation.Operator.NE, v2, c2); check(o1, o2,
 * "(v1==0)&&(v2!=1)", "v1==0"); }
 * 
 * @Test public void test05() { IntVariable v1 = new IntVariable("v1", 0, 99);
 * IntConstant c1 = new IntConstant(0); Operation o1 = new
 * Operation(Operation.Operator.EQ, v1, c1); IntConstant c2 = new
 * IntConstant(1); Operation o2 = new Operation(Operation.Operator.NE, v1, c2);
 * check(o1, o2, "(v1==0)&&(v1!=1)", "v1==0", "v1!=1"); }
 * 
 * @Test public void test06() { IntVariable v1 = new IntVariable("v1", 0, 99);
 * IntVariable v2 = new IntVariable("v2", 0, 99); Operation o1 = new
 * Operation(Operation.Operator.EQ, v1, v2); IntVariable v3 = new
 * IntVariable("v3", 0, 99); Operation o2 = new Operation(Operation.Operator.EQ,
 * v2, v3); IntVariable v4 = new IntVariable("v4", 0, 99); Operation o3 = new
 * Operation(Operation.Operator.EQ, v3, v4); IntVariable v5 = new
 * IntVariable("v5", 0, 99); Operation o4 = new Operation(Operation.Operator.EQ,
 * v4, v5); Operation o34 = new Operation(Operation.Operator.AND, o3, o4);
 * Operation o234 = new Operation(Operation.Operator.AND, o2, o34); check(o1,
 * o234, "(v1==v2)&&((v2==v3)&&((v3==v4)&&(v4==v5)))", "v1==v2", "v2==v3",
 * "v3==v4", "v4==v5"); }
 * 
 * @Test public void test07() { IntVariable v1 = new IntVariable("v1", 0, 99);
 * IntVariable v2 = new IntVariable("v2", 0, 99); Operation o1 = new
 * Operation(Operation.Operator.EQ, v1, v2); IntVariable v3 = new
 * IntVariable("v3", 0, 99); Operation o2 = new Operation(Operation.Operator.EQ,
 * v2, v3); IntVariable v4 = new IntVariable("v4", 0, 99); Operation o3 = new
 * Operation(Operation.Operator.EQ, v3, v4); IntVariable v5 = new
 * IntVariable("v5", 0, 99); IntVariable v6 = new IntVariable("v6", 0, 99);
 * Operation o4 = new Operation(Operation.Operator.EQ, v5, v6); Operation o34 =
 * new Operation(Operation.Operator.AND, o3, o4); Operation o234 = new
 * Operation(Operation.Operator.AND, o2, o34); check(o1, o234,
 * "(v1==v2)&&((v2==v3)&&((v3==v4)&&(v5==v6)))", "v2==v3", "v3==v4", "v1==v2");
 * }
 * 
 * @Test public void test08() { IntVariable v1 = new IntVariable("v1", 0, 99);
 * IntVariable v2 = new IntVariable("v2", 0, 99); IntVariable v3 = new
 * IntVariable("v3", 0, 99); IntVariable v4 = new IntVariable("v4", 0, 99);
 * IntVariable v5 = new IntVariable("v5", 0, 99); IntVariable v6 = new
 * IntVariable("v6", 0, 99); IntVariable v7 = new IntVariable("v7", 0, 99);
 * Operation o1 = new Operation(Operation.Operator.LT, v1, new
 * Operation(Operation.Operator.ADD, v2, v3)); Operation o2 = new
 * Operation(Operation.Operator.LT, v2, new Operation(Operation.Operator.ADD,
 * v4, v5)); Operation o3 = new Operation(Operation.Operator.LT, v3, new
 * Operation(Operation.Operator.ADD, v6, v7)); Operation o23 = new
 * Operation(Operation.Operator.AND, o2, o3); check(o1, o23,
 * "(v1<(v2+v3))&&((v2<(v4+v5))&&(v3<(v6+v7)))", "v1<(v2+v3)", "v3<(v6+v7)",
 * "v2<(v4+v5)"); }
 * 
 * @Test public void test09() { IntVariable v1 = new IntVariable("v1", 0, 99);
 * IntVariable v2 = new IntVariable("v2", 0, 99); IntVariable v3 = new
 * IntVariable("v3", 0, 99); IntVariable v4 = new IntVariable("v4", 0, 99);
 * IntVariable v5 = new IntVariable("v5", 0, 99); IntVariable v6 = new
 * IntVariable("v6", 0, 99); IntVariable v7 = new IntVariable("v7", 0, 99);
 * IntVariable v8 = new IntVariable("v8", 0, 99); Operation o1 = new
 * Operation(Operation.Operator.LT, v1, new Operation(Operation.Operator.ADD,
 * v2, v3)); Operation o2 = new Operation(Operation.Operator.LT, v2, new
 * Operation(Operation.Operator.ADD, v4, v5)); Operation o3 = new
 * Operation(Operation.Operator.LT, v6, new Operation(Operation.Operator.ADD,
 * v7, v8)); Operation o23 = new Operation(Operation.Operator.AND, o2, o3);
 * check(o1, o23, "(v1<(v2+v3))&&((v2<(v4+v5))&&(v6<(v7+v8)))", "v1<(v2+v3)",
 * "v2<(v4+v5)"); }
 * 
 */
