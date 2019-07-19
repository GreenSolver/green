/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.barvinok;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

import java.util.Properties;

import org.apfloat.Apint;
import org.junit.BeforeClass;
import org.junit.Rule;
import org.junit.Test;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.util.Configuration;

/**
 * Tests for {@link CountBarvinokService}.
 */
public class CountBarvinokWithBounderTest {

	/**
	 * The Green instance used throughout the test.
	 */
	public static Green solver;

	/**
	 * Set up the Green instance.
	 */
	@BeforeClass
	public static void initialize() {
		solver = new Green("GREEN-TEST");
		Properties properties = new Properties();
		properties.setProperty("green.services", "count");
		properties.setProperty("green.service.count", "(bounder (canonize barvinok))");
		properties.setProperty("green.service.count.bounder", "za.ac.sun.cs.green.service.bounder.BounderService");
		properties.setProperty("green.service.count.canonize", "za.ac.sun.cs.green.service.canonizer.SATCanonizerService");
		properties.setProperty("green.service.count.barvinok", "za.ac.sun.cs.green.service.barvinok.CountBarvinokService");
		Configuration config = new Configuration(solver, properties);
		config.configure();
	}

	/**
	 * JUnit4 rule to check if test should be executed. 
	 */
	@Rule
	public BarvinokTestRule barvinokTestRule = new BarvinokTestRule(solver);

	// ======================================================================
	//
	// ACTUAL TESTS
	//
	// ======================================================================

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v in [0, 99]) && (1 * v == 0)
	 * </pre>
	 *
	 * @result 1
	 */
	@Test
	public void test01() {
		IntVariable v = new IntVariable("v", 0, 99);
		Operation t = Operation.mul(Operation.ONE, v);
		Operation o = Operation.eq(t, Operation.ZERO);
		check(o, 1);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v in [0, 99]) && (1 * v > 0) && (1 * v - 10 < 0)
	 * </pre>
	 *
	 * @result 9
	 */
	@Test
	public void test02() {
		IntVariable v = new IntVariable("aa", 0, 99);
		IntConstant c0 = Operation.ZERO;
		IntConstant c1 = Operation.ONE;
		IntConstant cm10 = new IntConstant(-10);
		Operation o1 = Operation.gt(Operation.mul(c1, v), c0);
		Operation o2 = Operation.lt(Operation.add(Operation.mul(c1, v), cm10), c0);
		Operation o = Operation.and(o1, o2);
		check(o, 9);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v in [0, 99]) && (3 * v - 6 > 0) && (1 * v - 10 < 0)
	 * </pre>
	 *
	 * @result 7
	 */
	@Test
	public void test03() {
		IntVariable v = new IntVariable("v", 0, 99);
		IntConstant c0 = new IntConstant(0);
		IntConstant c1 = new IntConstant(1);
		IntConstant c3 = new IntConstant(3);
		IntConstant cm6 = new IntConstant(-6);
		IntConstant cm10 = new IntConstant(-10);
		Operation o1 = Operation.gt(Operation.add(Operation.mul(c3, v), cm6), c0);
		Operation o2 = Operation.lt(Operation.add(Operation.mul(c1, v), cm10), c0);
		Operation o = Operation.and(o1, o2);
		check(o, 7);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (a, b in [0, 9]) && (a - b < 0) && (a + 1 > 0) &&
	 * (a - 10 < 10) && (b + 1 > 0) && (b - 10 < 0)
	 * </pre>
	 *
	 * @result 45
	 */
	@Test
	public void test04() {
		IntVariable a = new IntVariable("a", 0, 9);
		IntVariable b = new IntVariable("b", 0, 9);
		IntConstant c0 = new IntConstant(0);
		IntConstant c1 = new IntConstant(1);
		IntConstant cm1 = new IntConstant(-1);
		IntConstant cm10 = new IntConstant(-10);
		Operation o1 = Operation.lt(Operation.add(Operation.mul(c1, a), Operation.mul(cm1, b)), c0);
		Operation o2 = Operation.gt(Operation.add(Operation.mul(c1, a), c1), c0);
		Operation o3 = Operation.lt(Operation.add(Operation.mul(c1, a), cm10), c0);
		Operation o4 = Operation.gt(Operation.add(Operation.mul(c1, b), c1), c0);
		Operation o5 = Operation.lt(Operation.add(Operation.mul(c1, b), cm10), c0);
		Operation o6 = Operation.and(o1, o2);
		Operation o7 = Operation.and(o6, o3);
		Operation o8 = Operation.and(o7, o4);
		Operation o = Operation.and(o8, o5);
		check(o, 45);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (a, b, c, d in [0, 9]) && (a + b < 6)   [A]
	 *                        && (b + c < 6)   [B]
	 *                        && (c + d < 6)   [C]
	 *                        && (a + c == 5)  [D]
	 *                        && (b + d == 1)  [E]
	 * </pre>
	 *
	 * @result [A] 21 [B] 91 [C] 371 [D] 42 [E] 9
	 */
	@Test
	public void test05() {
		IntVariable a = new IntVariable("a", 0, 9);
		IntVariable b = new IntVariable("b", 0, 9);
		IntVariable c = new IntVariable("c", 0, 9);
		IntVariable d = new IntVariable("d", 0, 9);
		IntConstant c0 = new IntConstant(0);
		IntConstant c1 = new IntConstant(1);
		IntConstant cm1 = new IntConstant(-1);
		IntConstant cm5 = new IntConstant(-5);
		IntConstant cm6 = new IntConstant(-6);
		Operation o1 = Operation.lt(Operation.add(Operation.add(Operation.mul(c1, a), Operation.mul(c1, b)), cm6), c0);
		Operation o2 = Operation.lt(Operation.add(Operation.add(Operation.mul(c1, b), Operation.mul(c1, c)), cm6), c0);
		Operation o3 = Operation.lt(Operation.add(Operation.add(Operation.mul(c1, c), Operation.mul(c1, d)), cm6), c0);
		Operation o4 = Operation.eq(Operation.add(Operation.add(Operation.mul(c1, a), Operation.mul(c1, c)), cm5), c0);
		Operation o5 = Operation.eq(Operation.add(Operation.add(Operation.mul(c1, b), Operation.mul(c1, d)), cm1), c0);
		Operation o12 = Operation.and(o1, o2);
		Operation o123 = Operation.and(o12, o3);
		Operation o1234 = Operation.and(o123, o4);
		Operation o12345 = Operation.and(o1234, o5);
		check(o1, 21);
		check(o12, 91);
		check(o123, 371);
		check(o1234, 42);
		check(o12345, 9);
	}
	
	// ======================================================================
	//
	// TEST SUPPORT ROUTINES
	//
	// ======================================================================

	private void check(Expression expression, Expression parentExpression, Apint expected) {
		Instance p = (parentExpression == null) ? null : new Instance(solver, null, parentExpression);
		Instance i = new Instance(solver, p, expression);
		Object result = i.request("count");
		assertNotNull(result);
		assertEquals(Apint.class, result.getClass());
		assertEquals(expected, result);
	}

	private void check(Expression expression, long expected) {
		check(expression, null, new Apint(expected));
	}
	
}
