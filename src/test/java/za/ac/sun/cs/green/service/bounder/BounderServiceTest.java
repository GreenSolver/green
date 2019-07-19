/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.bounder;

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
import za.ac.sun.cs.green.expr.RealConstant;
import za.ac.sun.cs.green.expr.RealVariable;
import za.ac.sun.cs.green.util.Configuration;

/**
 * Tests for {@link BounderService}.
 */
public class BounderServiceTest {

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
		props.setProperty("green.services", "bound");
		props.setProperty("green.service.bound", "(bounder sink)");
		props.setProperty("green.service.bound.bounder", "za.ac.sun.cs.green.service.bounder.BounderService");
		props.setProperty("green.service.bound.sink", "za.ac.sun.cs.green.service.sink.SinkService");
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
	 * (v0, v1 in {-10..99}) && (v0 == 0) && (v1 - 1 != 0)
	 * </pre>
	 *
	 * @result expression is satisfiable
	 */
	@Test
	public void test01() {
		IntVariable v = new IntVariable("v", 0, 99);
		IntConstant c0 = new IntConstant(0);
		Operation o = Operation.eq(v, c0);
		check(o, "v==0", "v==0", "v>=0", "v<=99");
	}

	@Test
	public void test02() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntVariable v2 = new IntVariable("v2", 9, 19);
		IntConstant c0 = new IntConstant(0);
		Operation o1 = Operation.eq(v1, c0);
		Operation o2 = Operation.eq(v2, c0);
		Operation o = Operation.and(o1, o2);
		check(o, "(v1==0)&&(v2==0)", "v1==0", "v1>=0", "v1<=99", "v2==0", "v2>=9", "v2<=19");
	}

	@Test
	public void test03() {
		RealVariable v = new RealVariable("v", 0.0, 99.0);
		RealConstant c0 = new RealConstant(0);
		Operation o = Operation.eq(v, c0);
		check(o, "v==0.0", "v==0.0", "v>=0.0", "v<=99.0");
	}

	// ======================================================================
	//
	// TEST SUPPORT ROUTINES
	//
	// ======================================================================

	private void check(Expression expression, String full, String... expected) {
		Instance i = new Instance(solver, null, expression);
		Expression e = i.getExpression();
		assertTrue(e.equals(expression));
		assertEquals(expression.toString(), e.toString());
		assertEquals(full, i.getFullExpression().toString());
		Object result = i.request("bound");
		assertNotNull(result);
		assertEquals(Instance.class, result.getClass());
		Instance j = (Instance) result;
		finalCheck(j.getFullExpression().toString(), expected);
	}

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

}
