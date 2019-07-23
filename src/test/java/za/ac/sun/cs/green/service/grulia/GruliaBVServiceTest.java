/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.grulia;

import org.junit.BeforeClass;
import org.junit.Ignore;
import org.junit.Test;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.service.ModelCoreService.ModelCore;
import za.ac.sun.cs.green.util.Configuration;

import java.util.Properties;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * Tests for {@link GruliaService} with bitvector solver. 
 */
@Ignore
public class GruliaBVServiceTest {

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
		props.setProperty("green.service.sat", "(grulia z3)");
		props.setProperty("green.service.sat.grulia", "za.ac.sun.cs.green.service.grulia.GruliaService");
		props.setProperty("green.service.sat.z3", "za.ac.sun.cs.green.service.z3.ModelCoreZ3JavaBVService");
		Configuration config = new Configuration(solver, props);
		config.configure();
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
	 * (v1, v2 in [-10, 99]) && (v1 == 0) && (v2 - 1 != 0)
	 * </pre>
	 * 
	 * @result satisfiable, satDelta = 2
	 */
	@Test
	public void test01() {
		IntVariable v1 = new IntVariable("v1", -10, 99);
		IntVariable v2 = new IntVariable("v2", -10, 99);
		IntConstant c0 = new IntConstant(0);
		IntConstant cm1 = new IntConstant(-1);
		Operation o1 = Operation.eq(v1, c0);
		Operation o2 = Operation.add(v2, cm1);
		Operation o3 = Operation.ne(o2, c0);
		Operation o = Operation.and(o1, o3);
		checkSat(o, 2);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v1, v2 in [-99, 99]) && (v1 + v2 + 1 == 0)
	 * </pre>
	 * 
	 * @result satisfiable, satDelta = 1
	 */
	@Test
	public void test02() {
		IntVariable v1 = new IntVariable("v1", -99, 99);
		IntVariable v2 = new IntVariable("v2", -99, 99);
		IntConstant c1 = new IntConstant(1);
		IntConstant c0 = new IntConstant(0);
		Operation o1 = Operation.add(v1, v2);
		Operation o2 = Operation.add(o1, c1);
		Operation o = Operation.le(o2, c0);
		checkSat(o, 1);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v1, v2 in [-99, 99]) && (5 * v1 < v2)
	 * </pre>
	 * 
	 * @result satisfiable, satDelta = 1
	 */
	@Test
	public void test03() {
		IntVariable v1 = new IntVariable("v1", -99, 99);
		IntVariable v2 = new IntVariable("v2", -99, 99);
		IntConstant c5 = new IntConstant(5);
		Operation o1 = Operation.mul(c5, v1);
		Operation o = Operation.lt(o1, v2);
		checkSat(o, 1);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v1, v2 in [0, 99]) && (5 * v1 - v2 + 1 <= 0)
	 * </pre>
	 * 
	 * @result satisfiable, satDelta = 1
	 */
	@Test
	public void test04() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntVariable v2 = new IntVariable("v2", 0, 99);
		IntConstant c0 = new IntConstant(0);
		IntConstant c1 = new IntConstant(1);
		IntConstant cm1 = new IntConstant(-1);
		IntConstant c5 = new IntConstant(5);
		Operation o1 = Operation.mul(c5, v1);
		Operation o2 = Operation.mul(cm1, v2);
		Operation o3 = Operation.add(o1, o2);
		Operation o4 = Operation.add(o3, c1);
		Operation o = Operation.le(o4, c0);
		checkSat(o, 1);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v1, v2 in [0, 99]) && (6 - v1 >= 0) && (4 - v2 + v1 == 0) && (v2 - 7 <= 0)
	 * </pre>
	 * 
	 * @result satisfiable, satDelta = 14
	 */
	@Test
	public void test05() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntVariable v2 = new IntVariable("v2", 0, 99);
		IntConstant c0 = new IntConstant(0);
		IntConstant c1 = new IntConstant(1);
		IntConstant cm1 = new IntConstant(-1);
		IntConstant c6 = new IntConstant(6);
		IntConstant cm7 = new IntConstant(-7);
		Operation o0 = Operation.mul(cm1, v1);
		Operation o1 = Operation.add(o0, c6);
		Operation o2 = Operation.le(o1, c0);
		Operation o3 = Operation.mul(cm1, v2);
		Operation o4 = Operation.add(v1, o3);
		Operation o5 = Operation.add(o4, c1);
		Operation o6 = Operation.eq(o5, c0);
		Operation o7 = Operation.add(v2, cm7);
		Operation o8 = Operation.le(o7, c0);
		Operation o9 = Operation.and(o2, o6);
		Operation o = Operation.and(o9, o8);
		checkSat(o, 14);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v1, v2 in [0, 99]) && (v1 > 5) && (v1 == v2 - 2) && (v2 <= 6)
	 * </pre>
	 * 
	 * @result unsatisfiable, satDelta = 14
	 */
	@Test
	public void test06() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntVariable v2 = new IntVariable("v2", 0, 99);
		IntConstant c2 = new IntConstant(2);
		IntConstant c5 = new IntConstant(5);
		IntConstant c6 = new IntConstant(6);
		Operation o1 = Operation.gt(v1, c5);
		Operation o2 = Operation.eq(v1, Operation.sub(v2, c2));
		Operation o3 = Operation.le(v2, c6);
		Operation o4 = Operation.and(o1, o2);
		Operation o = Operation.and(o4, o3);
		checkUnsat(o, 14);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v1, v2 in [0, 99]) && (v1 > 5) && (v1 == v2 - 2) && (v2 <= 6)
	 * </pre>
	 * 
	 * @result unsatisfiable, satDelta = 14
	 */
	@Test
	public void test07() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntVariable v2 = new IntVariable("v2", 0, 99);
		IntConstant c1 = new IntConstant(1);
		IntConstant c5 = new IntConstant(5);
		IntConstant c7 = new IntConstant(7);
		Operation o1 = Operation.gt(v1, c5);
		Operation o2 = Operation.eq(v1, Operation.sub(v2, c1));
		Operation o3 = Operation.le(v2, c7);
		Operation o4 = Operation.and(o1, o2);
		Operation o = Operation.and(o4, o3);
		checkSat(o, 14);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v1 in [0, 99]) && (v1 == 7)
	 * </pre>
	 * 
	 * @result satisfiable, satDelta = ?
	 */
	@Test
	public void test08() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntConstant c7 = new IntConstant(7);
		Operation o = Operation.eq(v1, c7);
		checkSat(o, -1);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v1, v2, v3 in [0, 99]) && (v1 == 7) && (v2 == v1 + 1) && (v3 <= v2 + 9)
	 * </pre>
	 * 
	 * @result satisfiable, satDelta = ?
	 */
	@Test
	public void test09() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntVariable v2 = new IntVariable("v2", 0, 99);
		IntVariable v3 = new IntVariable("v3", 0, 99);
		IntConstant c1 = new IntConstant(1);
		IntConstant c7 = new IntConstant(7);
		IntConstant c9 = new IntConstant(9);
		Operation o1 = Operation.eq(v1, c7);
		Operation o2 = Operation.add(v1, c1);
		Operation o3 = Operation.eq(v2, o2);
		Operation o4 = Operation.and(o1, o3);
		Operation o5 = Operation.add(v2, c9);
		Operation o6 = Operation.le(v3, o5);
		Operation o = Operation.and(o4, o6);
		checkSat(o, -1);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v1, v2, v3 in [0, 99]) && (v1 == 7) && (v2 == v1 + 1) && (v3 < v2 + 9)
	 * </pre>
	 * 
	 * @result satisfiable, satDelta = ?
	 */
	@Test
	public void test10() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntVariable v2 = new IntVariable("v2", 0, 99);
		IntVariable v3 = new IntVariable("v3", 0, 99);
		IntConstant c1 = new IntConstant(1);
		IntConstant c7 = new IntConstant(7);
		IntConstant c9 = new IntConstant(9);
		Operation o1 = Operation.eq(v1, c7);
		Operation o2 = Operation.add(v1, c1);
		Operation o3 = Operation.eq(v2, o2);
		Operation o4 = Operation.and(o1, o3);
		Operation o5 = Operation.add(v2, c9);
		Operation o6 = Operation.lt(v3, o5);
		Operation o = Operation.and(o4, o6);
		checkSat(o, -1);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v1, v2 in [-100, 1000]) && (v2 <= 65536) && (v2 >= -32768) && ((48 - 8 * v1) % 16 != 0)
	 * </pre>
	 * 
	 * @result satisfiable, satDelta = ?
	 */
	@Test
	public void test11() {
		int min = -100;
		int max = 1000;
		IntVariable v1 = new IntVariable("v1", min, max);
		IntVariable v2 = new IntVariable("v2", min, max);
		IntConstant c0 = new IntConstant(0);
		IntConstant c8 = new IntConstant(8);
		IntConstant c16 = new IntConstant(16);
		IntConstant c48 = new IntConstant(48);
		IntConstant cm32768 = new IntConstant(-32768);
		IntConstant c65536 = new IntConstant(65536);
		Operation o1 = Operation.le(v2, c65536);
		Operation o2 = Operation.ge(v2, cm32768);
		Operation o3 = Operation.and(o1, o2);
		Operation o4 = Operation.mul(v1, c8);
		Operation o40 = Operation.sub(c48, o4);
		Operation o400 = Operation.mod(o40, c16);
		Operation o5 = Operation.ne(o400, c0);
		Operation o = Operation.and(o5, o3);
		checkSat(o, -1);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v1 in [0, 99]) && (v1 > 10) && (v1 > 10)
	 * </pre>
	 * 
	 * @result unsatisfiable, satDelta = ?
	 */
	@Test
	public void unsatTest01() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntConstant c10 = new IntConstant(10);
		Operation o1 = Operation.lt(v1, c10);
		Operation o2 = Operation.gt(v1, c10);
		Operation o = Operation.and(o1, o2);
		checkUnsat(o, -1);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v1 in [0, 99]) && (v1 == 10) && (v1 > 10)
	 * </pre>
	 * 
	 * @result unsatisfiable, satDelta = ?
	 */
	@Test
	public void unsatTest02() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntConstant c10 = new IntConstant(10);
		Operation o1 = Operation.eq(v1, c10);
		Operation o2 = Operation.gt(v1, c10);
		Operation o = Operation.and(o1, o2);
		checkUnsat(o, -1);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v1 in [0, 99]) && (v1 == 10) && (v1 < 10) && (v1 > 10)
	 * </pre>
	 * 
	 * @result unsatisfiable, satDelta = ?
	 */
	@Test
	public void unsatTest03() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntConstant c10 = new IntConstant(10);
		Operation o1 = Operation.eq(v1, c10);
		Operation o2 = Operation.lt(v1, c10);
		Operation o3 = Operation.gt(v1, c10);
		Operation o4 = Operation.and(o1, o2);
		Operation o = Operation.and(o4, o3);
		checkUnsat(o, -1);
	}

	// ======================================================================
	//
	// TEST SUPPORT ROUTINES
	//
	// ======================================================================

	private void checkSat(Expression expression, int satDelta) {
		Instance instance = new Instance(solver, null, expression);
		Object result = instance.request("sat");
		assertTrue(result instanceof ModelCore);
		assertTrue(((ModelCore) result).isSat());
	}

	private void checkUnsat(Expression expression, int satDelta) {
		Instance instance = new Instance(solver, null, expression);
		Object result = instance.request("sat");
		assertTrue(result instanceof ModelCore);
		assertFalse(((ModelCore) result).isSat());
	}
	
}
