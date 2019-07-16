/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.taskmanager;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

import java.util.Properties;

import org.junit.BeforeClass;
import org.junit.Test;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.taskmanager.ParallelTaskManager;
import za.ac.sun.cs.green.util.Configuration;

/**
 * Tests for the parallel task manager.
 */
public class ParallelSATTest {

	/**
	 * The Green instance used throughout the test.
	 */
	public static Green solver;

	/**
	 * Set up the Green instance.
	 */
	@BeforeClass
	public static void initialize() {
		// solver = new Green();
		solver = new Green("GREEN-TEST");
		Properties props = new Properties();
		props.setProperty("green.taskmanager", ParallelTaskManager.class.getCanonicalName());
		props.setProperty("green.services", "sat");
		props.setProperty("green.service.sat", "(slice (canonize choco z3))");
		props.setProperty("green.service.sat.slice", "za.ac.sun.cs.green.service.slicer.SATSlicerService");
		props.setProperty("green.service.sat.canonize", "za.ac.sun.cs.green.service.canonizer.SATCanonizerService");
		props.setProperty("green.service.sat.choco", "za.ac.sun.cs.green.service.choco4.SATChoco4Service");
		props.setProperty("green.service.sat.z3", "za.ac.sun.cs.green.service.z3.SATZ3Service");
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
	 * 2 == 2
	 * </pre>
	 * 
	 * @result satisfiable
	 */
	@Test
	public void test00() {
		IntConstant c2a = new IntConstant(2);
		IntConstant c2b = new IntConstant(2);
		Operation o = Operation.eq(c2a, c2b);
		checkSat(o);
	}

	/**
	 * Check:
	 *
	 * <pre>
	 * (a in {0..99}) && (a == 0)
	 * </pre>
	 * 
	 * @result satisfiable
	 */
	@Test
	public void test01() {
		IntVariable v = new IntVariable("a", 0, 99);
		IntConstant c0 = new IntConstant(0);
		Operation o = Operation.eq(v, c0);
		checkSat(o);
	}

	/**
	 * Check:
	 *
	 * <pre>
	 * (a in {0..99}) && (a == 100)
	 * </pre>
	 * 
	 * @result unsatisfiable
	 */
	@Test
	public void test02() {
		IntVariable v = new IntVariable("a", 0, 99);
		IntConstant c100 = new IntConstant(100);
		Operation o = Operation.eq(v, c100);
		checkUnsat(o);
	}

	/**
	 * Check:
	 *
	 * <pre>
	 * (a in {0..99}) && (a == 10) && (a == 10)
	 * </pre>
	 * 
	 * @result satisfiable
	 */
	@Test
	public void test03() {
		IntVariable v = new IntVariable("a", 0, 99);
		IntConstant c10a = new IntConstant(10);
		IntConstant c10b = new IntConstant(10);
		Operation o1 = Operation.eq(v, c10a);
		Operation o2 = Operation.eq(v, c10b);
		Operation o3 = Operation.and(o1, o2);
		checkSat(o3);
	}

	/**
	 * Check:
	 *
	 * <pre>
	 * (a in {0..99}) && (a == 10) && (a == 20)
	 * </pre>
	 * 
	 * @result unsatisfiable
	 */
	@Test
	public void test04() {
		IntVariable v = new IntVariable("a", 0, 99);
		IntConstant c10 = new IntConstant(10);
		IntConstant c20 = new IntConstant(20);
		Operation o1 = Operation.eq(v, c10);
		Operation o2 = Operation.eq(v, c20);
		Operation o3 = Operation.and(o1, o2);
		checkUnsat(o3);
	}

	/**
	 * Check:
	 *
	 * <pre>
	 * (a in {0..99}) && (a >= 10) && (a < 20)
	 * </pre>
	 * 
	 * @result satisfiable
	 */
	@Test
	public void test05() {
		IntVariable v = new IntVariable("a", 0, 99);
		IntConstant c1 = new IntConstant(10);
		IntConstant c2 = new IntConstant(20);
		Operation o1 = Operation.ge(v, c1);
		Operation o2 = Operation.lt(v, c2);
		Operation o3 = Operation.and(o1, o2);
		checkSat(o3);
	}

	/**
	 * Check:
	 *
	 * <pre>
	 * Parent:    (a in {0..99}) && (a < 20)
	 * Condition: (a >= 10)
	 * </pre>
	 * 
	 * @result satisfiable
	 */
	@Test
	public void test06() {
		IntVariable v = new IntVariable("a", 0, 99);
		IntConstant c10 = new IntConstant(10);
		IntConstant c20 = new IntConstant(20);
		Operation o1 = Operation.ge(v, c10);
		Operation o2 = Operation.lt(v, c20);
		checkSat(o1, o2);
	}

	/**
	 * Check:
	 *
	 * <pre>
	 * Parent:    (b in {0..99}) && (b == 2012)
	 * Condition: (a in {0..99}) && (a >= 10)
	 * </pre>
	 * 
	 * @result satisfiable
	 */
	@Test
	public void test07() {
		IntVariable v1 = new IntVariable("a", 0, 99);
		IntVariable v2 = new IntVariable("b", 0, 99);
		IntConstant c10 = new IntConstant(10);
		IntConstant c2012 = new IntConstant(2012);
		Operation o1 = Operation.ge(v1, c10);
		Operation o2 = Operation.eq(v2, c2012);
		checkSat(o1, o2);
	}

	/**
	 * Check:
	 *
	 * <pre>
	 * (a,b in {0..99}) && (b == 2012) && (a >= 10)
	 * </pre>
	 * 
	 * @result unsatisfiable
	 */
	@Test
	public void test07a() {
		IntVariable v1 = new IntVariable("a", 0, 99);
		IntVariable v2 = new IntVariable("b", 0, 99);
		IntConstant c10 = new IntConstant(10);
		IntConstant c2012 = new IntConstant(2012);
		Operation o1 = Operation.ge(v1, c10);
		Operation o2 = Operation.eq(v2, c2012);
		Operation o = Operation.and(o2, o1);
		checkUnsat(o);
	}
	
	/**
	 * Check:
	 *
	 * <pre>
	 * Parent:    (a in {0..99}) && (a >= 10)
	 * Condition: (b in {0..99}) && (b == 2012)
	 * </pre>
	 * 
	 * @result unsatisfiable
	 */
	@Test
	public void test08() {
		IntVariable v1 = new IntVariable("a", 0, 99);
		IntVariable v2 = new IntVariable("b", 0, 99);
		IntConstant c10 = new IntConstant(10);
		IntConstant c2012 = new IntConstant(2012);
		Operation o1 = Operation.ge(v1, c10);
		Operation o2 = Operation.eq(v2, c2012);
		checkUnsat(o2, o1);
	}

	/**
	 * Check:
	 *
	 * <pre>
	 * Parent:    (a,c,d,e in {0..99}) && (c < d) && ((d < e) && (e < a))
	 * Condition: (b in {0..99}) && (a < b) && (b < c)
	 * </pre>
	 * 
	 * @result unsatisfiable
	 */
	@Test
	public void test09() {
		IntVariable v1 = new IntVariable("a", 0, 99);
		IntVariable v2 = new IntVariable("b", 0, 99);
		IntVariable v3 = new IntVariable("c", 0, 99);
		IntVariable v4 = new IntVariable("d", 0, 99);
		IntVariable v5 = new IntVariable("e", 0, 99);
		Operation o1 = Operation.lt(v1, v2);
		Operation o2 = Operation.lt(v2, v3);
		Operation o3 = Operation.lt(v3, v4);
		Operation o4 = Operation.lt(v4, v5);
		Operation o5 = Operation.lt(v5, v1);
		Operation o45 = Operation.and(o4, o5);
		Operation o345 = Operation.and(o3, o45);
		Operation o12 = Operation.and(o1, o2);
		checkUnsat(o12, o345);
	}

	/**
	 * Check:
	 *
	 * <pre>
	 * Parent:    (a,c,d,e in {0..99}) && (c <= d) && ((d <= e) && (e <= a))
	 * Condition: (b in {0..99}) && (a <= b) && (b <= c)
	 * </pre>
	 * 
	 * @result satisfiable
	 */
	@Test
	public void test10() {
		IntVariable v1 = new IntVariable("a", 0, 99);
		IntVariable v2 = new IntVariable("b", 0, 99);
		IntVariable v3 = new IntVariable("c", 0, 99);
		IntVariable v4 = new IntVariable("d", 0, 99);
		IntVariable v5 = new IntVariable("e", 0, 99);
		Operation o1 = Operation.le(v1, v2);
		Operation o2 = Operation.le(v2, v3);
		Operation o3 = Operation.le(v3, v4);
		Operation o4 = Operation.le(v4, v5);
		Operation o5 = Operation.le(v5, v1);
		Operation o45 = Operation.and(o4, o5);
		Operation o345 = Operation.and(o3, o45);
		Operation o12 = Operation.and(o1, o2);
		checkSat(o12, o345);
	}

	/**
	 * Check:
	 *
	 * <pre>
	 * Parent:    (c,d,e in {0..99}) && (d == 2 * c) && (e == 2 * d)
	 * Condition: (a,b in {0..99}) && (b == 2 * a) && (c == 2 * b)
	 * </pre>
	 * 
	 * @result satisfiable
	 */
	@Test
	public void test11() {
		IntVariable v1 = new IntVariable("a", 0, 99);
		IntVariable v2 = new IntVariable("b", 0, 99);
		IntVariable v3 = new IntVariable("c", 0, 99);
		IntVariable v4 = new IntVariable("d", 0, 99);
		IntVariable v5 = new IntVariable("e", 0, 99);
		IntConstant c2 = new IntConstant(2);
		Operation o1 = Operation.eq(v2, Operation.mul(c2, v1));
		Operation o2 = Operation.eq(v3, Operation.mul(c2, v2));
		Operation o3 = Operation.eq(v4, Operation.mul(c2, v3));
		Operation o4 = Operation.eq(v5, Operation.mul(c2, v4));
		Operation o12 = Operation.and(o1, o2);
		Operation o34 = Operation.and(o3, o4);
		checkSat(o12, o34);
	}

	/**
	 * Check:
	 *
	 * <pre>
	 * Parent:    (c,d,e in {0..9}) && (d == 2 * c) && (e == 2 * d)
	 * Condition: (a,b in {0..9}) && (b == 2 * a) && (c == 2 * b)
	 * </pre>
	 * 
	 * @result satisfiable
	 */
	@Test
	public void test12() {
		IntVariable v1 = new IntVariable("a", 0, 9);
		IntVariable v2 = new IntVariable("b", 0, 9);
		IntVariable v3 = new IntVariable("c", 0, 9);
		IntVariable v4 = new IntVariable("d", 0, 9);
		IntVariable v5 = new IntVariable("e", 0, 9);
		IntConstant c2 = new IntConstant(2);
		Operation o1 = Operation.eq(v2, Operation.mul(c2, v1));
		Operation o2 = Operation.eq(v3, Operation.mul(c2, v2));
		Operation o3 = Operation.eq(v4, Operation.mul(c2, v3));
		Operation o4 = Operation.eq(v5, Operation.mul(c2, v4));
		Operation o12 = Operation.and(o1, o2);
		Operation o34 = Operation.and(o3, o4);
		checkSat(o12, o34);
	}

	/**
	 * Check:
	 *
	 * <pre>
	 * Parent:    (c,d,e in {0..9}) && (d == 2 * c) && (e == 2 * d)
	 * Condition: (a in {1..9}) && (b in {0..9}) && (b == 2 * a) && (c == 2 * b)
	 * </pre>
	 * 
	 * @result unsatisfiable
	 */
	@Test
	public void test13() {
		IntVariable v1 = new IntVariable("a", 1, 9);
		IntVariable v2 = new IntVariable("b", 0, 9);
		IntVariable v3 = new IntVariable("c", 0, 9);
		IntVariable v4 = new IntVariable("d", 0, 9);
		IntVariable v5 = new IntVariable("e", 0, 9);
		IntConstant c2 = new IntConstant(2);
		Operation o1 = Operation.eq(v2, Operation.mul(c2, v1));
		Operation o2 = Operation.eq(v3, Operation.mul(c2, v2));
		Operation o3 = Operation.eq(v4, Operation.mul(c2, v3));
		Operation o4 = Operation.eq(v5, Operation.mul(c2, v4));
		Operation o12 = Operation.and(o1, o2);
		Operation o34 = Operation.and(o3, o4);
		checkUnsat(o12, o34);
	}

	/**
	 * Check:
	 *
	 * <pre>
	 * Parent:    (a,b,c in {0..2048}) && ((a == c) && ((a == b) && (a > 0))) && ((b > 0) && (c > 0))
	 * Condition: (b != c)
	 * </pre>
	 * 
	 * @result unsatisfiable
	 */
	@Test
	public void test14() {
		IntVariable v1 = new IntVariable("a", 0, 2048);
		IntVariable v2 = new IntVariable("b", 0, 2048);
		IntVariable v3 = new IntVariable("c", 0, 2048);
		IntConstant c0 = new IntConstant(0);
		Operation o1 = Operation.ne(v2, v3);
		Operation o2 = Operation.eq(v1, v3);
		Operation o3 = Operation.eq(v1, v2);
		Operation o4 = Operation.gt(v1, c0);
		Operation o5 = Operation.gt(v2, c0);
		Operation o6 = Operation.gt(v3, c0);
		Operation o34 = Operation.and(o3, o4);
		Operation o56 = Operation.and(o5, o6);
		Operation o234 = Operation.and(o2, o34);
		Operation o23456 = Operation.and(o234, o56);
		checkUnsat(o1, o23456);
	}

	// ======================================================================
	//
	// TEST SUPPORT ROUTINES
	//
	// ======================================================================

	/**
	 * Check that the expression is satisfiable.
	 *
	 * @param expression expression to check
	 */
	private void checkSat(Expression expression) {
		check(expression, null, true);
	}

	/**
	 * Check that the expression is unsatisfiable.
	 *
	 * @param expression expression to check
	 */
	private void checkUnsat(Expression expression) {
		check(expression, null, false);
	}

	/**
	 * Check that the expression is satisfiable under the assumption that the parent
	 * expression is satisfiable (even if it is not).
	 *
	 * @param expression       expression to check
	 * @param parentExpression parent expression
	 */
	private void checkSat(Expression expression, Expression parentExpression) {
		check(expression, parentExpression, true);
	}

	/**
	 * Check that the expression is unsatisfiable under the assumption that the
	 * parent expression is satisfiable (even if it is not).
	 *
	 * @param expression       expression to check
	 * @param parentExpression parent expression
	 */
	private void checkUnsat(Expression expression, Expression parentExpression) {
		check(expression, parentExpression, false);
	}

	/**
	 * Construct a Green instance with the given expression and parent expression,
	 * and check that Green produces the expected result
	 *
	 * @param expression       expression to check
	 * @param parentExpression parent expression
	 * @param expected         correct outcome
	 */
	private void check(Expression expression, Expression parentExpression, boolean expected) {
		Instance p = (parentExpression == null) ? null : new Instance(solver, null, parentExpression);
		Instance i = new Instance(solver, p, expression);
		Object result = i.request("sat");
		assertNotNull(result);
		assertEquals(Boolean.class, result.getClass());
		assertEquals(expected, result);
	}

}
