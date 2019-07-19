/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.factorizer;

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
 * Complex tests for the SAT factorizer.
 */
public class ComplexSATFactorizerTest {

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
		Properties props = new Properties();
		props.setProperty("green.services", "sat");
		props.setProperty("green.service.sat", "(factor (canonize z3))");
		props.setProperty("green.service.sat.factor", "za.ac.sun.cs.green.service.factorizer.SATFactorizerService");
		props.setProperty("green.service.sat.canonize", "za.ac.sun.cs.green.service.canonizer.SATCanonizerService");
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
	 * Check the following system of equations:
	 * 
	 * (v0 <= v1) && (v1 <= v2) && ... && (vN-1 <= v0) && (vN < 10)
	 * 
	 * vi = 0..99
	 * 
	 * Should be satisfiable.
	 */
	@Test
	public void test01() {
		final int n = 10;
		IntVariable[] v = new IntVariable[n + 1];
		for (int i = 0; i < n + 1; i++) {
			v[i] = new IntVariable("v" + i, 0, 99);
		}
		Operation[] o = new Operation[n + 1];
		for (int i = 0; i < n; i++) {
			o[i] = Operation.le(v[i], v[(i + 1) % n]);
		}
		IntConstant c10 = new IntConstant(10);
		o[n] = Operation.lt(v[n], c10);
		Operation oo = o[0];
		for (int i = 1; i < n; i++) {
			oo = Operation.and(oo, o[i]);
		}
		checkSat(o[n], oo);
	}

	/**
	 * Check the following system of equations:
	 * 
	 * (v0 < v1) && (v1 < v2) && ... && (vN-1 < v0) && (vN < 10)
	 * 
	 * vi = 0..99
	 * 
	 * Should be unsatisfiable due to cycle in first N conjuncts.
	 */
	@Test
	public void test02() {
		final int n = 10;
		IntVariable[] v = new IntVariable[n + 1];
		for (int i = 0; i < n + 1; i++) {
			v[i] = new IntVariable("v" + i, 0, 99);
		}
		Operation[] o = new Operation[n + 1];
		for (int i = 0; i < n; i++) {
			o[i] = Operation.lt(v[i], v[(i + 1) % n]);
		}
		IntConstant c10 = new IntConstant(10);
		o[n] = Operation.lt(v[n], c10);
		Operation oo = o[0];
		for (int i = 1; i < n; i++) {
			oo = Operation.and(oo, o[i]);
		}
		checkUnsat(o[n], oo);
	}

	/**
	 * Check the following system of equations:
	 * 
	 * (v0 < v1) && (v1 < v2) && ... && (vN-1 < vN) && (vN < N)
	 * 
	 * vi = 0..10
	 * 
	 * Should be unsatisfiable because the only possible values are: v0 = 0 v1 = 1
	 * v2 = 2 ... vN = N
	 * 
	 * but last conjunct claims vN < N.
	 */
	@Test
	public void test03() {
		final int n = 10;
		IntVariable[] v = new IntVariable[n + 1];
		for (int i = 0; i < n + 1; i++) {
			v[i] = new IntVariable("v" + i, 0, n);
		}
		Operation[] o = new Operation[n + 1];
		for (int i = 0; i < n; i++) {
			o[i] = Operation.lt(v[i], v[i + 1]);
		}
		IntConstant cN = new IntConstant(n);
		o[n] = Operation.lt(v[n], cN);
		Operation oo = o[0];
		for (int i = 1; i < n; i++) {
			oo = Operation.and(oo, o[i]);
		}
		checkUnsat(o[n], oo);
	}

	/**
	 * Check the following system of equations:
	 * 
	 * (v0 <= w0) && (w0 <= v0) && (v1 <= w1) && (w1 <= v1) && ... && (vN-1 <= wN-1)
	 * && (wN-1 <= vN-1)
	 * 
	 * vi = 0..99, wi = 0..99
	 * 
	 * Should be satisfiable.
	 */
	@Test
	public void test04() {
		final int n = 10;
		IntVariable[] v = new IntVariable[n];
		IntVariable[] w = new IntVariable[n];
		for (int i = 0; i < n; i++) {
			v[i] = new IntVariable("v" + i, 0, 99);
			w[i] = new IntVariable("w" + i, 0, 99);
		}
		Operation[] o = new Operation[n + 1];
		for (int i = 0; i < n; i++) {
			Operation o0 = Operation.le(v[i], w[i]);
			Operation o1 = Operation.le(w[i], v[i]);
			o[i] = Operation.and(o0, o1);
		}
		Operation oo = o[0];
		for (int i = 1; i < n; i++) {
			oo = Operation.and(oo, o[i]);
		}
		checkSat(oo);
	}

	/**
	 * Check the following system of equations:
	 * 
	 * (v0 < w0) && (w0 < v0) && (v1 < w1) && (w1 < v1) && ... && (vN-1 < wN-1) &&
	 * (wN-1 < vN-1)
	 * 
	 * vi = 0..99 wi = 0..99
	 * 
	 * Should be unsatisfiable.
	 */
	@Test
	public void test05() {
		final int n = 10;
		IntVariable[] v = new IntVariable[n];
		IntVariable[] w = new IntVariable[n];
		for (int i = 0; i < n; i++) {
			v[i] = new IntVariable("v" + i, 0, 99);
			w[i] = new IntVariable("w" + i, 0, 99);
		}
		Operation[] o = new Operation[n + 1];
		for (int i = 0; i < n; i++) {
			Operation o0 = Operation.lt(v[i], w[i]);
			Operation o1 = Operation.lt(w[i], v[i]);
			o[i] = Operation.and(o0, o1);
		}
		Operation oo = o[0];
		for (int i = 1; i < n; i++) {
			oo = Operation.and(oo, o[i]);
		}
		checkUnsat(oo);
	}

	// ======================================================================
	//
	// TEST SUPPORT ROUTINES
	//
	// ======================================================================

	private void check(Expression expression, Expression parentExpression, boolean expected) {
		Instance p = (parentExpression == null) ? null : new Instance(solver, null, parentExpression);
		Instance i = new Instance(solver, p, expression);
		Object result = i.request("sat");
		assertTrue(result instanceof Boolean);
		assertEquals(expected, result);
	}

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

}
