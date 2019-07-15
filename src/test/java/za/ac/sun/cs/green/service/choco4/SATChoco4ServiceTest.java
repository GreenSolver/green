/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.choco4;

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
 * Tests for {@link SATChoco4Service}.
 */
public class SATChoco4ServiceTest {

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
		props.setProperty("green.services", "sat");
		props.setProperty("green.service.sat", "choco4");
		props.setProperty("green.service.sat.choco4", "za.ac.sun.cs.green.service.choco4.SATChoco4Service");
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
	 * @result satisfied
	 */
	@Test
	public void test00() {
		IntConstant c2a = new IntConstant(2);
		IntConstant c2b = new IntConstant(2);
		Operation o = new Operation(Operation.Operator.EQ, c2a, c2b);
		checkSat(o);
	}

	/**
	 * Check:
	 *
	 * <pre>
	 * (a in {0..99}) && (a == 0)
	 * </pre>
	 * 
	 * @result satisfied
	 */
	@Test
	public void test01() {
		IntVariable v = new IntVariable("a", 0, 99);
		IntConstant c0 = new IntConstant(0);
		Operation o = new Operation(Operation.Operator.EQ, v, c0);
		checkSat(o);
	}

	/**
	 * Check:
	 *
	 * <pre>
	 * (a in {0..99}) && (a == 100)
	 * </pre>
	 * 
	 * @result unsatisfied
	 */
	@Test
	public void test02() {
		IntVariable v = new IntVariable("a", 0, 99);
		IntConstant c100 = new IntConstant(100);
		Operation o = new Operation(Operation.Operator.EQ, v, c100);
		checkUnsat(o);
	}

	/**
	 * Check:
	 *
	 * <pre>
	 * (a in {0..99}) && (a == 10) && (a == 10)
	 * </pre>
	 * 
	 * @result satisfied
	 */
	@Test
	public void test03() {
		IntVariable v = new IntVariable("a", 0, 99);
		IntConstant c10a = new IntConstant(10);
		IntConstant c10b = new IntConstant(10);
		Operation o1 = new Operation(Operation.Operator.EQ, v, c10a);
		Operation o2 = new Operation(Operation.Operator.EQ, v, c10b);
		Operation o3 = new Operation(Operation.Operator.AND, o1, o2);
		checkSat(o3);
	}

	/**
	 * Check:
	 *
	 * <pre>
	 * (a in {0..99}) && (a == 10) && (a == 20)
	 * </pre>
	 * 
	 * @result unsatisfied
	 */
	@Test
	public void test04() {
		IntVariable v = new IntVariable("a", 0, 99);
		IntConstant c10 = new IntConstant(10);
		IntConstant c20 = new IntConstant(20);
		Operation o1 = new Operation(Operation.Operator.EQ, v, c10);
		Operation o2 = new Operation(Operation.Operator.EQ, v, c20);
		Operation o3 = new Operation(Operation.Operator.AND, o1, o2);
		checkUnsat(o3);
	}

	/**
	 * Check:
	 *
	 * <pre>
	 * (a in {0..99}) && (a >= 10) && (a < 20)
	 * </pre>
	 * 
	 * @result satisfied
	 */
	@Test
	public void test05() {
		IntVariable v = new IntVariable("a", 0, 99);
		IntConstant c1 = new IntConstant(10);
		IntConstant c2 = new IntConstant(20);
		Operation o1 = new Operation(Operation.Operator.GE, v, c1);
		Operation o2 = new Operation(Operation.Operator.LT, v, c2);
		Operation o3 = new Operation(Operation.Operator.AND, o1, o2);
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
	 * @result satisfied
	 */
	@Test
	public void test06() {
		IntVariable v = new IntVariable("a", 0, 99);
		IntConstant c10 = new IntConstant(10);
		IntConstant c20 = new IntConstant(20);
		Operation o1 = new Operation(Operation.Operator.GE, v, c10);
		Operation o2 = new Operation(Operation.Operator.LT, v, c20);
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
	 * @result unsatisfied
	 */
	@Test
	public void test07() {
		IntVariable v1 = new IntVariable("a", 0, 99);
		IntVariable v2 = new IntVariable("b", 0, 99);
		IntConstant c10 = new IntConstant(10);
		IntConstant c2012 = new IntConstant(2012);
		Operation o1 = new Operation(Operation.Operator.GE, v1, c10);
		Operation o2 = new Operation(Operation.Operator.EQ, v2, c2012);
		checkUnsat(o1, o2);
	}

	/**
	 * Check:
	 *
	 * <pre>
	 * Parent:    (a in {0..99}) && (a >= 10)
	 * Condition: (b in {0..99}) && (b == 2012)
	 * </pre>
	 * 
	 * @result unsatisfied
	 */
	@Test
	public void test08() {
		IntVariable v1 = new IntVariable("a", 0, 99);
		IntVariable v2 = new IntVariable("b", 0, 99);
		IntConstant c10 = new IntConstant(10);
		IntConstant c2012 = new IntConstant(2012);
		Operation o1 = new Operation(Operation.Operator.GE, v1, c10);
		Operation o2 = new Operation(Operation.Operator.EQ, v2, c2012);
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
	 * @result unsatisfied
	 */
	@Test
	public void test09() {
		IntVariable v1 = new IntVariable("a", 0, 99);
		IntVariable v2 = new IntVariable("b", 0, 99);
		IntVariable v3 = new IntVariable("c", 0, 99);
		IntVariable v4 = new IntVariable("d", 0, 99);
		IntVariable v5 = new IntVariable("e", 0, 99);
		Operation o1 = new Operation(Operation.Operator.LT, v1, v2);
		Operation o2 = new Operation(Operation.Operator.LT, v2, v3);
		Operation o3 = new Operation(Operation.Operator.LT, v3, v4);
		Operation o4 = new Operation(Operation.Operator.LT, v4, v5);
		Operation o5 = new Operation(Operation.Operator.LT, v5, v1);
		Operation o45 = new Operation(Operation.Operator.AND, o4, o5);
		Operation o345 = new Operation(Operation.Operator.AND, o3, o45);
		Operation o12 = new Operation(Operation.Operator.AND, o1, o2);
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
	 * @result satisfied
	 */
	@Test
	public void test10() {
		IntVariable v1 = new IntVariable("a", 0, 99);
		IntVariable v2 = new IntVariable("b", 0, 99);
		IntVariable v3 = new IntVariable("c", 0, 99);
		IntVariable v4 = new IntVariable("d", 0, 99);
		IntVariable v5 = new IntVariable("e", 0, 99);
		Operation o1 = new Operation(Operation.Operator.LE, v1, v2);
		Operation o2 = new Operation(Operation.Operator.LE, v2, v3);
		Operation o3 = new Operation(Operation.Operator.LE, v3, v4);
		Operation o4 = new Operation(Operation.Operator.LE, v4, v5);
		Operation o5 = new Operation(Operation.Operator.LE, v5, v1);
		Operation o45 = new Operation(Operation.Operator.AND, o4, o5);
		Operation o345 = new Operation(Operation.Operator.AND, o3, o45);
		Operation o12 = new Operation(Operation.Operator.AND, o1, o2);
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
	 * @result satisfied
	 */
	@Test
	public void test11() {
		IntVariable v1 = new IntVariable("a", 0, 99);
		IntVariable v2 = new IntVariable("b", 0, 99);
		IntVariable v3 = new IntVariable("c", 0, 99);
		IntVariable v4 = new IntVariable("d", 0, 99);
		IntVariable v5 = new IntVariable("e", 0, 99);
		IntConstant c2 = new IntConstant(2);
		Operation o1 = new Operation(Operation.Operator.EQ, v2, new Operation(Operation.Operator.MUL, c2, v1));
		Operation o2 = new Operation(Operation.Operator.EQ, v3, new Operation(Operation.Operator.MUL, c2, v2));
		Operation o3 = new Operation(Operation.Operator.EQ, v4, new Operation(Operation.Operator.MUL, c2, v3));
		Operation o4 = new Operation(Operation.Operator.EQ, v5, new Operation(Operation.Operator.MUL, c2, v4));
		Operation o12 = new Operation(Operation.Operator.AND, o1, o2);
		Operation o34 = new Operation(Operation.Operator.AND, o3, o4);
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
	 * @result satisfied
	 */
	@Test
	public void test12() {
		IntVariable v1 = new IntVariable("a", 0, 9);
		IntVariable v2 = new IntVariable("b", 0, 9);
		IntVariable v3 = new IntVariable("c", 0, 9);
		IntVariable v4 = new IntVariable("d", 0, 9);
		IntVariable v5 = new IntVariable("e", 0, 9);
		IntConstant c2 = new IntConstant(2);
		Operation o1 = new Operation(Operation.Operator.EQ, v2, new Operation(Operation.Operator.MUL, c2, v1));
		Operation o2 = new Operation(Operation.Operator.EQ, v3, new Operation(Operation.Operator.MUL, c2, v2));
		Operation o3 = new Operation(Operation.Operator.EQ, v4, new Operation(Operation.Operator.MUL, c2, v3));
		Operation o4 = new Operation(Operation.Operator.EQ, v5, new Operation(Operation.Operator.MUL, c2, v4));
		Operation o12 = new Operation(Operation.Operator.AND, o1, o2);
		Operation o34 = new Operation(Operation.Operator.AND, o3, o4);
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
	 * @result unsatisfied
	 */
	@Test
	public void test13() {
		IntVariable v1 = new IntVariable("a", 1, 9);
		IntVariable v2 = new IntVariable("b", 0, 9);
		IntVariable v3 = new IntVariable("c", 0, 9);
		IntVariable v4 = new IntVariable("d", 0, 9);
		IntVariable v5 = new IntVariable("e", 0, 9);
		IntConstant c2 = new IntConstant(2);
		Operation o1 = new Operation(Operation.Operator.EQ, v2, new Operation(Operation.Operator.MUL, c2, v1));
		Operation o2 = new Operation(Operation.Operator.EQ, v3, new Operation(Operation.Operator.MUL, c2, v2));
		Operation o3 = new Operation(Operation.Operator.EQ, v4, new Operation(Operation.Operator.MUL, c2, v3));
		Operation o4 = new Operation(Operation.Operator.EQ, v5, new Operation(Operation.Operator.MUL, c2, v4));
		Operation o12 = new Operation(Operation.Operator.AND, o1, o2);
		Operation o34 = new Operation(Operation.Operator.AND, o3, o4);
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
	 * @result unsatisfied
	 */
	@Test
	public void test14() {
		IntVariable v1 = new IntVariable("a", 0, 2048);
		IntVariable v2 = new IntVariable("b", 0, 2048);
		IntVariable v3 = new IntVariable("c", 0, 2048);
		IntConstant c0 = new IntConstant(0);
		Operation o1 = new Operation(Operation.Operator.NE, v2, v3);
		Operation o2 = new Operation(Operation.Operator.EQ, v1, v3);
		Operation o3 = new Operation(Operation.Operator.EQ, v1, v2);
		Operation o4 = new Operation(Operation.Operator.GT, v1, c0);
		Operation o5 = new Operation(Operation.Operator.GT, v2, c0);
		Operation o6 = new Operation(Operation.Operator.GT, v3, c0);
		Operation o34 = new Operation(Operation.Operator.AND, o3, o4);
		Operation o56 = new Operation(Operation.Operator.AND, o5, o6);
		Operation o234 = new Operation(Operation.Operator.AND, o2, o34);
		Operation o23456 = new Operation(Operation.Operator.AND, o234, o56);
		checkUnsat(o1, o23456);
	}

	// ======================================================================
	//
	// TEST SUPPORT ROUTINES
	//
	// ======================================================================

	private void checkSat(Expression expression) {
		check(expression, null, true);
	}

	private void checkUnsat(Expression expression) {
		check(expression, null, false);
	}

	private void checkSat(Expression expression, Expression parentExpression) {
		check(expression, parentExpression, true);
	}

	private void checkUnsat(Expression expression, Expression parentExpression) {
		check(expression, parentExpression, false);
	}

	private void check(Expression expression, Expression parentExpression, boolean expected) {
		Instance parent = (parentExpression == null) ? null : new Instance(solver, null, parentExpression);
		Instance instance = new Instance(solver, parent, expression);
		Object result = instance.request("sat");
		assertTrue(result instanceof Boolean);
		assertEquals(expected, result);
	}

}
