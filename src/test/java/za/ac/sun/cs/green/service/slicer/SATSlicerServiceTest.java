/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.slicer;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
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
 * Tests for {@link SATSlicerService}.
 */
public class SATSlicerServiceTest {

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
		props.setProperty("green.service.sat", "(slice sink)");
		props.setProperty("green.service.sat.slice", "za.ac.sun.cs.green.service.slicer.SATSlicerService");
		props.setProperty("green.service.sat.sink", "za.ac.sun.cs.green.service.sink.SinkService");
		Configuration config = new Configuration(solver, props);
		config.configure();
	}

	// ======================================================================
	//
	// ACTUAL TESTS
	//
	// ======================================================================

	@Test
	public void test01() {
		IntVariable v = new IntVariable("v", 0, 99);
		IntConstant c = new IntConstant(0);
		Operation o = Operation.eq(v, c);
		check(o, "v==0", "v==0");
	}

	@Test
	public void test02a() {
		IntConstant c1 = new IntConstant(2);
		IntConstant c2 = new IntConstant(2);
		Operation o = Operation.eq(c1, c2);
		check(o, "2==2", "2==2");
	}

	@Test
	public void test02b() {
		IntConstant c1 = new IntConstant(2);
		IntConstant c2 = new IntConstant(2);
		Operation o = Operation.lt(c1, c2);
		check(o, "2<2", "2<2");
	}

	@Test
	public void test03() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntConstant c1 = new IntConstant(0);
		Operation o1 = Operation.eq(v1, c1);
		IntVariable v2 = new IntVariable("v2", 0, 99);
		IntConstant c2 = new IntConstant(1);
		Operation o2 = Operation.ne(v2, c2);
		check(o1, o2, "(v1==0)&&(v2!=1)", "v1==0");
	}

	@Test
	public void test04() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntConstant c1 = new IntConstant(0);
		Operation o1 = Operation.eq(v1, c1);
		IntVariable v2 = new IntVariable("v2", 0, 99);
		IntConstant c2 = new IntConstant(1);
		Operation o2 = Operation.ne(v2, c2);
		check(o1, o2, "(v1==0)&&(v2!=1)", "v1==0");
	}

	@Test
	public void test05() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntConstant c1 = new IntConstant(0);
		Operation o1 = Operation.eq(v1, c1);
		IntConstant c2 = new IntConstant(1);
		Operation o2 = Operation.ne(v1, c2);
		check(o1, o2, "(v1==0)&&(v1!=1)", "v1==0", "v1!=1");
	}

	@Test
	public void test06() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntVariable v2 = new IntVariable("v2", 0, 99);
		Operation o1 = Operation.eq(v1, v2);
		IntVariable v3 = new IntVariable("v3", 0, 99);
		Operation o2 = Operation.eq(v2, v3);
		IntVariable v4 = new IntVariable("v4", 0, 99);
		Operation o3 = Operation.eq(v3, v4);
		IntVariable v5 = new IntVariable("v5", 0, 99);
		Operation o4 = Operation.eq(v4, v5);
		Operation o34 = Operation.and(o3, o4);
		Operation o234 = Operation.and(o2, o34);
		check(o1, o234, "(v1==v2)&&((v2==v3)&&((v3==v4)&&(v4==v5)))", "v1==v2", "v2==v3", "v3==v4", "v4==v5");
	}

	@Test
	public void test07() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntVariable v2 = new IntVariable("v2", 0, 99);
		Operation o1 = Operation.eq(v1, v2);
		IntVariable v3 = new IntVariable("v3", 0, 99);
		Operation o2 = Operation.eq(v2, v3);
		IntVariable v4 = new IntVariable("v4", 0, 99);
		Operation o3 = Operation.eq(v3, v4);
		IntVariable v5 = new IntVariable("v5", 0, 99);
		IntVariable v6 = new IntVariable("v6", 0, 99);
		Operation o4 = Operation.eq(v5, v6);
		Operation o34 = Operation.and(o3, o4);
		Operation o234 = Operation.and(o2, o34);
		check(o1, o234, "(v1==v2)&&((v2==v3)&&((v3==v4)&&(v5==v6)))", "v2==v3", "v3==v4", "v1==v2");
	}

	@Test
	public void test08() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntVariable v2 = new IntVariable("v2", 0, 99);
		IntVariable v3 = new IntVariable("v3", 0, 99);
		IntVariable v4 = new IntVariable("v4", 0, 99);
		IntVariable v5 = new IntVariable("v5", 0, 99);
		IntVariable v6 = new IntVariable("v6", 0, 99);
		IntVariable v7 = new IntVariable("v7", 0, 99);
		Operation o1 = Operation.lt(v1, Operation.add(v2, v3));
		Operation o2 = Operation.lt(v2, Operation.add(v4, v5));
		Operation o3 = Operation.lt(v3, Operation.add(v6, v7));
		Operation o23 = Operation.and(o2, o3);
		check(o1, o23, "(v1<(v2+v3))&&((v2<(v4+v5))&&(v3<(v6+v7)))", "v1<(v2+v3)", "v3<(v6+v7)", "v2<(v4+v5)");
	}

	@Test
	public void test09() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntVariable v2 = new IntVariable("v2", 0, 99);
		IntVariable v3 = new IntVariable("v3", 0, 99);
		IntVariable v4 = new IntVariable("v4", 0, 99);
		IntVariable v5 = new IntVariable("v5", 0, 99);
		IntVariable v6 = new IntVariable("v6", 0, 99);
		IntVariable v7 = new IntVariable("v7", 0, 99);
		IntVariable v8 = new IntVariable("v8", 0, 99);
		Operation o1 = Operation.lt(v1, Operation.add(v2, v3));
		Operation o2 = Operation.lt(v2, Operation.add(v4, v5));
		Operation o3 = Operation.lt(v6, Operation.add(v7, v8));
		Operation o23 = Operation.and(o2, o3);
		check(o1, o23, "(v1<(v2+v3))&&((v2<(v4+v5))&&(v6<(v7+v8)))", "v1<(v2+v3)", "v2<(v4+v5)");
	}

	// ======================================================================
	//
	// TEST SUPPORT ROUTINES
	//
	// ======================================================================

	private void finalCheck(String observed, String[] expected) {
		for (String s : expected) {
			int p = observed.indexOf(s);
			assertTrue(p >= 0);
			if (p == 0) {
				observed = observed.substring(p + s.length());
			} else if (p > 0) {
				observed = observed.substring(0, p - 1) + observed.substring(p + s.length());
			}
		}
		observed = observed.replaceAll("[()&]", "");
		assertEquals("", observed);
	}

	private void check(Expression expression, String full, String... expected) {
		Instance instance = new Instance(solver, null, expression);
		Expression expr = instance.getExpression();
		assertTrue(expr.equals(expression));
		assertEquals(expression.toString(), expr.toString());
		assertEquals(full, instance.getFullExpression().toString());
		Object result = instance.request("sat");
		assertNotNull(result);
		assertEquals(Instance.class, result.getClass());
		Instance j = (Instance) result;
		finalCheck(j.getExpression().toString(), expected);
	}

	private void check(Expression expression, Expression parentExpression, String full, String... expected) {
		Instance parentInstance = new Instance(solver, null, parentExpression);
		Instance instance = new Instance(solver, parentInstance, expression);
		Expression e = instance.getExpression();
		assertTrue(e.equals(expression));
		assertEquals(expression.toString(), e.toString());
		assertEquals(full, instance.getFullExpression().toString());
		Object result = instance.request("sat");
		assertNotNull(result);
		assertEquals(Instance.class, result.getClass());
		Instance j = (Instance) result;
		finalCheck(j.getExpression().toString(), expected);
	}

}
