/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
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
		props.setProperty("green.service.idtest.choco", "za.ac.sun.cs.green.service.choco4.SATChoco4Service");
		new Configuration(solver0, props).configure();
		
		solver1 = new Green("GREEN-TEST");
		props.setProperty("green.service.idtest", "(identity choco)");
		props.setProperty("green.service.idtest.identity", "za.ac.sun.cs.green.service.identity.IdentityService");
		new Configuration(solver1, props).configure();
	}

	// ======================================================================
	//
	// ACTUAL TESTS
	//
	// ======================================================================

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v in [0, 99]) && (v == 0)
	 * </pre>
	 *
	 * @result both solvers should report that the expression is satisfiable
	 */
	@Test
	public void test01() {
		IntVariable v = new IntVariable("v", 0, 99);
		IntConstant c = new IntConstant(0);
		Operation o = Operation.eq(v, c);
		check(o, true);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v1 in [0, 99]) && (v2 in [0, 99]) && (v1 == 0) && (v2 == 0)
	 * </pre>
	 *
	 * @result both solvers should report that the expression is satisfiable
	 */
	@Test
	public void test02() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntVariable v2 = new IntVariable("v2", 0, 99);
		IntConstant c1 = new IntConstant(0);
		IntConstant c2 = new IntConstant(0);
		Operation o1 = Operation.eq(v1, c1);
		Operation o2 = Operation.eq(v2, c2);
		Operation o = Operation.and(o1, o2);
		check(o, true);
	}
	
	/**
	 * Test:
	 * 
	 * <pre>
	 * (2 == 2)
	 * </pre>
	 *
	 * @result both solvers should report that the expression is satisfiable
	 */
	@Test
	public void test03() {
		IntConstant c1 = new IntConstant(2);
		IntConstant c2 = new IntConstant(2);
		Operation o = Operation.eq(c1, c2);
		check(o, true);
	}
	
	/**
	 * Test:
	 * 
	 * <pre>
	 * (2 == 3)
	 * </pre>
	 *
	 * @result both solvers should report that the expression is unsatisfiable
	 */
	@Test
	public void test04() {
		IntConstant c1 = new IntConstant(2);
		IntConstant c2 = new IntConstant(3);
		Operation o = Operation.eq(c1, c2);
		check(o, false);
	}
	
	/**
	 * Test:
	 * 
	 * <pre>
	 * (v1 in [0, 99]) && (v2 in [9, 99]) && (v1 == 0) && (v2 == 0)
	 * </pre>
	 *
	 * @result both solvers should report that the expression is unsatisfiable
	 */
	@Test
	public void test05() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntVariable v2 = new IntVariable("v2", 9, 99);
		IntConstant c1 = new IntConstant(0);
		IntConstant c2 = new IntConstant(0);
		Operation o1 = Operation.eq(v1, c1);
		Operation o2 = Operation.eq(v2, c2);
		Operation o = Operation.and(o1, o2);
		check(o, false);
	}
	
	// ======================================================================
	//
	// TEST SUPPORT ROUTINES
	//
	// ======================================================================

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

}
