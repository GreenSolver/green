/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.z3javabv;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.function.Function;

import org.apache.logging.log4j.Logger;
import org.junit.BeforeClass;
import org.junit.Ignore;
import org.junit.Test;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.service.ModelCoreService.ModelCore;
import za.ac.sun.cs.green.util.Configuration;

/**
 * Tests for {@link ModelCoreZ3JavaBVService}.
 */
@Ignore
public class ModelZ3JavaBVServiceTest {

	/**
	 * The Green instance used throughout the test.
	 */
	public static Green solver;

	/**
	 * Set up the Green instance.
	 */
	@BeforeClass
	public static void initialize() {
		solver = new Green();
		// solver = new Green("GREEN-TEST");
		Properties props = new Properties();
		props.setProperty("green.services", "modelcore");
		props.setProperty("green.service.modelcore", "z3");
		props.setProperty("green.service.modelcore.z3", "za.ac.sun.cs.green.service.z3javabv.ModelCoreZ3JavaBVService");
		Configuration config = new Configuration(solver, props);
		config.configure();
	}

	// ======================================================================
	//
	// ACTUAL TESTS
	//
	// ======================================================================

	/**
	 * Check:
	 * 
	 * <pre>
	 * (v in {-10..99}) && (v == 0)
	 * </pre>
	 *
	 * @result any model that satisfies the constraints
	 */
	@Test
	public void test00() {
		IntVariable v = new IntVariable("v", -10, 99);
		IntConstant c0 = Operation.ZERO;
		Operation o = Operation.eq(v, c0);
		checkSat(o, m -> {
			int w = ((IntConstant) m.get(v)).getValue();
			return (w == 0);
		});
	}

	/**
	 * Check:
	 * 
	 * <pre>
	 * (v0, v1 in {-10..99}) && (v0 == 0) && (v1 - 1 != 0)
	 * </pre>
	 *
	 * @result any model that satisfies the constraints
	 */
	@Test
	public void test01() {
		// example: "(aa==0)&&(bb!=1)" => "1*v==0", "1*v+-1!=0" => 0 & 2
		IntVariable v0 = new IntVariable("v0", -10, 99);
		IntVariable v1 = new IntVariable("v1", -10, 99);
		IntConstant c0a = Operation.ZERO;
		IntConstant c0b = Operation.ZERO;
		IntConstant cm1 = new IntConstant(-1);
		Operation o1 = Operation.eq(v0, c0a);
		Operation o2 = Operation.add(v1, cm1);
		Operation o3 = Operation.ne(o2, c0b);
		Operation o = Operation.and(o1, o3);
		checkSat(o, m -> {
			int w0 = ((IntConstant) m.get(v0)).getValue();
			int w1 = ((IntConstant) m.get(v1)).getValue();
			return (w0 >= -10) && (w0 <= 99) && (w1 >= -10) && (w1 <= 99) && (w0 == 0) && (w1 - 1 != 0);
		});
	}
	
	/**
	 * Check:
	 * 
	 * <pre>
	 * (v0, v1 in {-99..99}) && (v0 + v1 + 0 < 1)
	 * </pre>
	 *
	 * @result any model that satisfies the constraints
	 */
	@Test
	public void test02() {
		// example: "(aa+bb)<(aa-cc)" => "1*v+1*v+1<=0" => 1
		IntVariable v0 = new IntVariable("v0", -99, 99);
		IntVariable v1 = new IntVariable("v1", -99, 99);
		IntConstant c0 = Operation.ONE;
		IntConstant c1 = Operation.ZERO;
		Operation o1 = Operation.add(v0, v1);
		Operation o2 = Operation.add(o1, c0);
		Operation o = Operation.le(o2, c1);
		checkSat(o, m -> {
			int w0 = ((IntConstant) m.get(v0)).getValue();
			int w1 = ((IntConstant) m.get(v1)).getValue();
			return (w0 >= -99) && (w0 <= 99) && (w1 >= -99) && (w1 <= 99) && (w0 + w1 + 0 < 1);
		});
	}

	/**
	 * Check:
	 * 
	 * <pre>
	 * (a, b in {-99..99}) && (a * 5 < b)
	 * </pre>
	 *
	 * @result any model that satisfies the constraints
	 */
	@Test
	public void test03() {
		// example: "((2+3)*aa)<bb" => 5*0<0
		IntVariable v1 = new IntVariable("a", -99, 99);
		IntVariable v2 = new IntVariable("b", -99, 99);
		IntConstant c5 = new IntConstant(5);
		Operation o1 = Operation.mul(c5, v1);
		Operation o2 = Operation.lt(o1, v2);
		checkSat(o2, m -> {
			int a = ((IntConstant) m.get(v1)).getValue();
			int b = ((IntConstant) m.get(v2)).getValue();
			return (a >= -99) && (a <= 99) && (b >= -99) && (b <= 99) && (a * 5 < b);
		});
	}

	/**
	 * Check:
	 * 
	 * <pre>
	 * (a, b in {0..99}) && (5 * v0 + -1 * v1 + 1 < 0)
	 * </pre>
	 *
	 * @result any model that satisfies the constraints
	 */
	@Test
	public void test04() {
		// example: "((2+3)*aa)<bb" => "5*v+-1*v+1<=0" => 5*0 + 0 + 1 < 0
		IntVariable v0 = new IntVariable("v0", 0, 99);
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntConstant c5 = new IntConstant(5);
		IntConstant cm1 = new IntConstant(-1);
		IntConstant c1 = Operation.ONE;
		IntConstant c0 = Operation.ZERO;
		Operation o1 = Operation.mul(c5, v0);
		Operation o2 = Operation.mul(cm1, v1);
		Operation o3 = Operation.add(o1, o2);
		Operation o4 = Operation.add(o3, c1);
		Operation o = Operation.le(o4, c0);
		checkSat(o, m -> {
			int w0 = ((IntConstant) m.get(v0)).getValue();
			int w1 = ((IntConstant) m.get(v1)).getValue();
			return (w0 >= 0) && (w0 <= 99) && (w1 >= 0) && (w1 <= 99) && (5 * w0 - w1 + 1 <= 0);
		});
	}

	/**
	 * Check:
	 * 
	 * <pre>
	 * (v0, v1 in {0..99}) &&
	 * ((-1 * v0 + 6 <= 0) &&
	 * (v0 + -1 * v1 + 1 == 0)) &&
	 * (v1 - 7 <= 0)
	 * </pre>
	 *
	 * @result any model that satisfies the constraints
	 */
	@Test
	public void test05() {
		// ((x>5)&&(x==(y-1)))&&(y<=7) => -1*v+6<=0, 1*v+-1*v+1==0, 1*v+-7<=0
		IntVariable v0 = new IntVariable("v0", 0, 99);
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntConstant cm1 = new IntConstant(-1);
		IntConstant c6 = new IntConstant(6);
		IntConstant c1 = Operation.ONE;
		IntConstant cm7 = new IntConstant(-7);
		IntConstant c0 = Operation.ZERO;
		Operation o1 = Operation.mul(cm1, v0);
		Operation o2 = Operation.add(o1, c6);
		Operation o3 = Operation.le(o2, c0);
		Operation o4 = Operation.mul(cm1, v1);
		Operation o5 = Operation.add(v0, o4);
		Operation o55 = Operation.add(o5, c1);
		Operation o6 = Operation.eq(o55, c0);
		Operation o7 = Operation.add(v1, cm7);
		Operation o8 = Operation.le(o7, c0);
		Operation o9 = Operation.and(o3, o6);
		Operation o = Operation.and(o9, o8);
		checkSat(o, m -> {
			int w0 = ((IntConstant) m.get(v0)).getValue();
			int w1 = ((IntConstant) m.get(v1)).getValue();
			boolean b0 = (w0 >= 0) && (w0 <= 99);
			boolean b1 = (w1 >= 0) && (w1 <= 99);
			boolean q0 = (6 - w0 <= 0);
			boolean q1 = (w0 - w1 + 1 == 0);
			boolean q2 = (w1 - 7 <= 0);
			return b0 && b1 && q0 && q1 && q2;
		});
	}

	/**
	 * Check:
	 * 
	 * <pre>
	 * (x, y in {0..99}) && (y < 6) && ((x > 5) && (x == y - 2))
	 * </pre>
	 *
	 * @result core that shows that the expression is unsatisfiable
	 */
	@Test
	public void test06() {
		// ((x>5)&&(x==(y-2)))&&(y<=6) // UNSAT
		IntVariable v1 = new IntVariable("x", 0, 99);
		IntVariable v2 = new IntVariable("y", 0, 99);
		IntConstant c5 = new IntConstant(5);
		IntConstant c2 = new IntConstant(2);
		IntConstant c6 = new IntConstant(6);
		Operation o1 = Operation.gt(v1, c5);
		Operation o2 = Operation.eq(v1, Operation.sub(v2, c2));
		Operation o3 = Operation.le(v2, c6);
		Operation o4 = Operation.and(o1, o2);
		Operation o = Operation.and(o4, o3);
		checkUnsat(o, setof(o1, o2, o3));
	}

	/**
	 * Check:
	 * 
	 * <pre>
	 * (x, y in {0..99}) && ((x > 5) && (x < 4)) && (x == y)
	 * </pre>
	 *
	 * @result core that shows that the expression is unsatisfiable
	 */
	@Test
	public void test06a() {
		IntVariable v1 = new IntVariable("x", 0, 99);
		IntVariable v2 = new IntVariable("y", 0, 99);
		IntConstant c5 = new IntConstant(5);
		IntConstant c4 = new IntConstant(4);
		Operation o1 = Operation.gt(v1, c5);
		Operation o2 = Operation.lt(v1, c4);
		Operation o3 = Operation.eq(v1, v2);
		Operation o4 = Operation.and(o1, o2);
		Operation o = Operation.and(o4, o3);
		checkUnsat(o, setof(o1, o2));
	}

	/**
	 * Check:
	 * 
	 * <pre>
	 * (x, y in {0..99}) && ((x == 200) && (x == 300)) && (x == y)
	 * </pre>
	 *
	 * @result core that shows that the expression is unsatisfiable
	 */
	@Test
	public void test06b() {
		IntVariable v1 = new IntVariable("x", 0, 99);
		IntVariable v2 = new IntVariable("y", 0, 99);
		IntConstant c200 = new IntConstant(200);
		IntConstant c300 = new IntConstant(300);
		Operation o1 = Operation.eq(v1, c200);
		Operation o2 = Operation.eq(v1, c300);
		Operation o3 = Operation.eq(v1, v2);
		Operation o4 = Operation.and(o1, o2);
		Operation o = Operation.and(o4, o3);
		Operation b1u = Operation.ge(v1, new IntConstant(99));
		checkUnsat(o, setof(b1u, o1), setof(b1u, o2), setof(o1, o2));
	}

	/**
	 * Check:
	 * 
	 * <pre>
	 * (x, y in {0..99}) && ((x == 2) && (y == 3)) && (x == y)
	 * </pre>
	 *
	 * @result core that shows that the expression is unsatisfiable
	 */
	@Test
	public void test06c() {
		IntVariable v1 = new IntVariable("x", 0, 99);
		IntVariable v2 = new IntVariable("y", 0, 99);
		IntConstant c2 = new IntConstant(2);
		IntConstant c3 = new IntConstant(3);
		Operation o1 = Operation.eq(v1, c2);
		Operation o2 = Operation.eq(v2, c3);
		Operation o3 = Operation.eq(v1, v2);
		Operation o4 = Operation.and(o1, o2);
		Operation o = Operation.and(o4, o3);
		checkUnsat(o, setof(o1, o2, o3));
	}

	/**
	 * Check:
	 * 
	 * <pre>
	 * (x, y in {0..99}) && ((x > 5) && (x == y - 1)) && (y <= 7)
	 * </pre>
	 *
	 * @result any model that satisfies the constraints
	 */
	@Test
	public void test07() {
		// ((x>5)&&(x==(y-1)))&&(y<=7)
		IntVariable v1 = new IntVariable("x", 0, 99);
		IntVariable v2 = new IntVariable("y", 0, 99);
		IntConstant c5 = new IntConstant(5);
		IntConstant c1 = new IntConstant(1);
		IntConstant c7 = new IntConstant(7);
		Operation o1 = Operation.gt(v1, c5);
		Operation o2 = Operation.eq(v1, Operation.sub(v2, c1));
		Operation o3 = Operation.le(v2, c7);
		Operation o4 = Operation.and(o1, o2);
		Operation o = Operation.and(o4, o3);
		checkSat(o, m -> {
			int x = ((IntConstant) m.get(v1)).getValue();
			int y = ((IntConstant) m.get(v2)).getValue();
			boolean bx = (x >= 0) && (x <= 99);
			boolean by = (y >= 0) && (y <= 99);
			boolean q0 = (x > 5);
			boolean q1 = (x == y - 1);
			boolean q2 = (y <= 7);
			return bx && by && q0 && q1 && q2;
		});
	}

	/**
	 * Check:
	 * 
	 * <pre>
	 * (v in {0..99}) && (v == 7)
	 * </pre>
	 *
	 * @result any model that satisfies the constraints
	 */
	@Test
	public void test08() {
		IntVariable v1 = new IntVariable("v", 0, 99);
		IntConstant c1 = new IntConstant(7);
		Operation o = Operation.eq(v1, c1);
		checkSat(o, m -> {
			int v = ((IntConstant) m.get(v1)).getValue();
			return (v >= 0) && (v <= 99) && (v == 7);
		});
	}

	/**
	 * Check:
	 * 
	 * <pre>
	 * (x, y, z in {0..99}) && ((x == 7) && (y == x + 1)) && (z <= y + 9)
	 * </pre>
	 *
	 * @result any model that satisfies the constraints
	 */
	@Test
	public void test10() {
		// x = 7 & y = x + 1 & z <= y+9
		IntVariable v1 = new IntVariable("x", 0, 99);
		IntVariable v2 = new IntVariable("y", 0, 99);
		IntVariable v3 = new IntVariable("z", 0, 99);
		IntConstant c7 = new IntConstant(7);
		IntConstant c1 = new IntConstant(1);
		IntConstant c9 = new IntConstant(9);
		Operation o1 = Operation.eq(v1, c7);
		Operation o2 = Operation.add(v1, c1);
		Operation o3 = Operation.eq(v2, o2);
		Operation o4 = Operation.and(o1, o3);
		Operation o5 = Operation.add(v2, c9);
		Operation o6 = Operation.le(v3, o5);
		Operation o = Operation.and(o4, o6);
		checkSat(o, m -> {
			int x = ((IntConstant) m.get(v1)).getValue();
			int y = ((IntConstant) m.get(v2)).getValue();
			int z = ((IntConstant) m.get(v3)).getValue();
			boolean bx = (x >= 0) && (x <= 99);
			boolean by = (y >= 0) && (y <= 99);
			boolean bz = (z >= 0) && (z <= 99);
			boolean q0 = (x == 7);
			boolean q1 = (y == x + 1);
			boolean q2 = (z <= y + 9);
			return bx && by && bz && q0 && q1 && q2;
		});
	}

	/**
	 * Check:
	 * 
	 * <pre>
	 * (x, y, z in {0..99}) && ((x == 7) && (y == x + 1)) && (z < y + 9)
	 * </pre>
	 *
	 * @result any model that satisfies the constraints
	 */
	@Test
	public void test11() {
		// x = 7 & y = x + 1 & z <= y+9
		IntVariable v1 = new IntVariable("x", 0, 99);
		IntVariable v2 = new IntVariable("y", 0, 99);
		IntVariable v3 = new IntVariable("z", 0, 99);
		IntConstant c7 = new IntConstant(7);
		IntConstant c1 = new IntConstant(1);
		IntConstant c9 = new IntConstant(9);
		Operation o1 = Operation.eq(v1, c7);
		Operation o2 = Operation.add(v1, c1);
		Operation o3 = Operation.eq(v2, o2);
		Operation o4 = Operation.and(o1, o3);
		Operation o5 = Operation.add(v2, c9);
		Operation o6 = Operation.lt(v3, o5);
		Operation o = Operation.and(o4, o6);
		checkSat(o, m -> {
			int x = ((IntConstant) m.get(v1)).getValue();
			int y = ((IntConstant) m.get(v2)).getValue();
			int z = ((IntConstant) m.get(v3)).getValue();
			boolean bx = (x >= 0) && (x <= 99);
			boolean by = (y >= 0) && (y <= 99);
			boolean bz = (z >= 0) && (z <= 99);
			boolean q0 = (x == 7);
			boolean q1 = (y == x + 1);
			boolean q2 = (z < y + 9);
			return bx && by && bz && q0 && q1 && q2;
		});
	}

	/**
	 * Check:
	 * 
	 * <pre>
	 * (x in {0..99}) && (x < 10) && (x > 10)
	 * </pre>
	 *
	 * @result core that shows that the expression is unsatisfiable
	 */
	@Test
	public void unsatTest01() {
		IntVariable v1 = new IntVariable("x", 0, 99);
		IntConstant c10 = new IntConstant(10);
		Operation o1 = Operation.lt(v1, c10);
		Operation o2 = Operation.gt(v1, c10);
		Operation o = Operation.and(o1, o2);
		checkUnsat(o, setof(o1, o2));
	}

	/**
	 * Check:
	 * 
	 * <pre>
	 * (x in {0..99}) && (x == 0) && (x > 0)
	 * </pre>
	 *
	 * @result core that shows that the expression is unsatisfiable
	 */
	@Test
	public void unsatTest02() {
		IntVariable v1 = new IntVariable("x", 0, 99);
		IntConstant c0 = new IntConstant(0);
		Operation o1 = Operation.eq(v1, c0);
		Operation o2 = Operation.gt(v1, c0);
		Operation o = Operation.and(o1, o2);
		checkUnsat(o, setof(o1, o2));
	}

	/**
	 * Check:
	 * 
	 * <pre>
	 * (x in {0..99}) && (x == 0) && (x > 0) && (x < 0)
	 * </pre>
	 *
	 * @result core that shows that the expression is unsatisfiable
	 */
	@Test
	public void unsatTest03() {
		IntVariable v1 = new IntVariable("x", 0, 99);
		IntConstant c0 = new IntConstant(0);
		Operation o1 = Operation.eq(v1, c0);
		Operation o2 = Operation.lt(v1, c0);
		Operation o3 = Operation.gt(v1, c0);
		Operation o4 = Operation.and(o1, o2);
		Operation o = Operation.and(o4, o3);
		Operation b1l = Operation.ge(v1, Operation.ZERO);
		checkUnsat(o, setof(o2, b1l));
	}

	// ======================================================================
	//
	// TEST SUPPORT ROUTINES
	//
	// ======================================================================

	/**
	 * Create a set containing the given elements.
	 *
	 * @param expressions array of elements
	 * @return a {@link HashSet} with the elements
	 */
	@SafeVarargs
	private final Set<Expression> setof(Expression... expressions) {
		return new HashSet<Expression>(Arrays.asList(expressions));
	}

	/**
	 * Check that an expression is satisfiable and that the model produced does
	 * indeed satisfy the expression. The caller must supply a list of
	 * {@link Function} that checks that the model is correct.
	 *
	 * @param expression expression to solve
	 * @param checker    {@link Function} that checks that model is correct
	 */
	private void checkSat(Expression expression, Function<Map<Variable, Constant>, Boolean> checker) {
		Instance instance = new Instance(solver, null, expression);
		assertTrue(instance != null);
		Object result = instance.request("modelcore");
		assertTrue(result instanceof ModelCore);
		ModelCore modelCore = (ModelCore) result;
		assertTrue(modelCore.isSat());
		assertTrue(checker.apply(modelCore.getModel()));
	}

	/**
	 * Check that an expression is unsatisfiable and that the core is indeed as
	 * expected.
	 *
	 * @param expression      expression to solve
	 * @param expectedCoreSet set of set of expected core conjuncts
	 */
	@SafeVarargs
	private final void checkUnsat(Expression expression, Set<Expression>... expectedCoreSet) {
		Instance instance = new Instance(solver, null, expression);
		assertTrue(instance != null);
		Object result = instance.request("modelcore");
		assertTrue(result instanceof ModelCore);
		ModelCore modelCore = (ModelCore) result;
		assertFalse(modelCore.isSat());
		Set<Expression> cores = modelCore.getCore();
		int n = cores.size();
		assertEquals(n, cores.size());
		String[] actual = new String[n];
		int j = 0;
		for (Expression core : cores) {
			actual[j++] = core.toString();
		}
		Arrays.sort(actual);
		String actualString = String.join(";;", actual);
		Set<String> expectedStrings = new HashSet<>();
		String[] expected = new String[n];
		for (Set<Expression> expectedCores : expectedCoreSet) {
			j = 0;
			for (Expression core : expectedCores) {
				expected[j++] = core.toString();
			}
			Arrays.sort(expected);
			expectedStrings.add(String.join(";;", expected));
		}
		Logger log = solver.getLogger();
		log.debug("expected: {}", () -> expectedStrings.toString());
		log.debug("actual: {}", () -> actualString.toString());
		assertTrue(expectedStrings.contains(actualString));
	}

}
