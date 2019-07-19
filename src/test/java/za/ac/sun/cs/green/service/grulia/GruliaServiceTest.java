/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.grulia;

import static org.junit.Assert.assertFalse;
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
import za.ac.sun.cs.green.service.ModelCoreService.ModelCore;
import za.ac.sun.cs.green.util.Configuration;

/**
 * Tests for {@link GruliaService}. 
 */
public class GruliaServiceTest {

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
		props.setProperty("green.service.sat.z3", "za.ac.sun.cs.green.service.z3.ModelCoreZ3Service");
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
	 * (a in [-10, 10]) && (a == 0)
	 * </pre>
	 * 
	 * One of the Grulia reference solutions is supposed to "hit" this input.
	 *
	 * @result satisfiable
	 */
	@Test
	public void testJG00() {
		IntVariable v1 = new IntVariable("a", -10, 10);
		Operation o = Operation.eq(v1, Operation.ZERO);
		checkSat(o);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v0, v1 in [-10, 99]) && (v0 == 0) && (v1 - 1 != 0)
	 * </pre>
	 * 
	 * SatDelta: 2
	 *
	 * @result satisfiable
	 */
	@Test
	public void test01() {
		IntVariable v0 = new IntVariable("v0", -10, 99);
		IntVariable v1 = new IntVariable("v1", -10, 99);
		IntConstant c0 = new IntConstant(0);
		IntConstant c0a = new IntConstant(0);
		IntConstant cm1 = new IntConstant(-1);
		Operation o1 = Operation.eq(v0, c0);
		Operation o2 = Operation.ne(Operation.add(v1, cm1), c0a);
		Operation o = Operation.and(o1, o2);
		checkSat(o);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v0, v1 in [-99, 99]) && (v0 + v1 + 1 <= 0)
	 * </pre>
	 * 
	 * SatDelta: 1
	 *
	 * @result satisfiable
	 */
	@Test
	public void test02() {
		IntVariable v0 = new IntVariable("v0", -99, 99);
		IntVariable v1 = new IntVariable("v1", -99, 99);
		IntConstant c0 = new IntConstant(0);
		IntConstant c1 = new IntConstant(1);
		Operation o = Operation.le(Operation.add(Operation.add(v0, v1), c1), c0);
		checkSat(o);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (a, b in [-99, 99]) && (5 * v0 < v1)
	 * </pre>
	 * 
	 * SatDelta: 1
	 *
	 * @result satisfiable
	 */
	@Test
	public void test03() {
		IntVariable v0 = new IntVariable("a", -99, 99);
		IntVariable v1 = new IntVariable("b", -99, 99);
		IntConstant c5 = new IntConstant(5);
		Operation o = Operation.lt(Operation.mul(c5, v0), v1);
		checkSat(o);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v0, v1 in [0, 99]) && (5 * v0 + -1 * v1 + 1 <= 0)
	 * </pre>
	 * 
	 * SatDelta: 1
	 *
	 * @result satisfiable
	 */
	@Test
	public void test04() {
		IntVariable v0 = new IntVariable("v0", 0, 99);
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntConstant c0 = new IntConstant(0);
		IntConstant c1 = new IntConstant(1);
		IntConstant cm1 = new IntConstant(-1);
		IntConstant c5 = new IntConstant(5);
		Operation o1 = Operation.mul(c5, v0);
		Operation o2 = Operation.mul(cm1, v1);
		Operation o3 = Operation.add(o1, o2);
		Operation o4 = Operation.add(o3, c1);
		Operation o = Operation.le(o4, c0);
		checkSat(o);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v0, v1 in [0, 99]) && (-1 * v0 + 6 <= 0) && (v0 + -1 * v1 + 1 == 0) && (v1 - 7 <= 0)
	 * </pre>
	 * 
	 * SatDelta: 14
	 *
	 * @result satisfiable
	 */
	@Test
	public void test05() {
		IntVariable v0 = new IntVariable("v0", 0, 99);
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntConstant c0 = new IntConstant(0);
		IntConstant c1 = new IntConstant(1);
		IntConstant cm1 = new IntConstant(-1);
		IntConstant c6 = new IntConstant(6);
		IntConstant cm7 = new IntConstant(-7);
		Operation o1 = Operation.le(Operation.add(Operation.mul(cm1, v0), c6), c0);
		Operation o2 = Operation.eq(Operation.add(Operation.add(v0, Operation.mul(cm1, v1)), c1), c0);
		Operation o3 = Operation.le(Operation.add(v1, cm7), c0);
		Operation o = Operation.and(Operation.and(o1, o2), o3);
		checkSat(o);
	}

	/**
	 * Test:
	 * 
	 * <pre>
	 * (v0, v1 in [0, 99]) && (v0 >= 5) && (v0 == v1 - 2) && (v1 <= 6)
	 * </pre>
	 * 
	 * SatDelta: 14
	 *
	 * @result unsatisfiable
	 */
	@Test
	public void test06() {
		IntVariable v0 = new IntVariable("x", 0, 99);
		IntVariable v1 = new IntVariable("y", 0, 99);
		IntConstant c2 = new IntConstant(2);
		IntConstant c5 = new IntConstant(5);
		IntConstant c6 = new IntConstant(6);
		Operation o1 = Operation.gt(v0, c5);
		Operation o2 = Operation.eq(v0, Operation.sub(v1, c2));
		Operation o3 = Operation.le(v1, c6);
		Operation o = Operation.and(Operation.and(o1, o2), o3);
		checkUnsat(o);
	}

	@Test
	public void test07() {
		// ((x>5)&&(x==(y-1)))&&(y<=7)
		// SAT-Delta: 14 (for reference model 0)
		IntVariable v1 = new IntVariable("x", 0, 99);
		IntVariable v2 = new IntVariable("y", 0, 99);
		IntConstant c1 = new IntConstant(5);
		IntConstant c2 = new IntConstant(1);
		IntConstant c3 = new IntConstant(7);

		Operation o1 = Operation.gt(v1, c1);
		Operation o2 = Operation.eq(v1, Operation.sub(v2, c2));
		Operation o3 = Operation.le(v2, c3);

		Operation o4 = Operation.and(o1, o2);
		Operation o = Operation.and(o4, o3);
		checkSat(o);
	}

	@Test
	public void test08() {
		IntVariable v1 = new IntVariable("v", 0, 99);
		IntConstant c1 = new IntConstant(7);
		Operation o = Operation.eq(v1, c1);
		checkSat(o);
	}

	@Test
	public void test09() {
		// x = 7 & y = x + 1 & z <= y+9
		IntVariable v1 = new IntVariable("x", 0, 99);
		IntVariable v2 = new IntVariable("y", 0, 99);
		IntVariable v3 = new IntVariable("z", 0, 99);
		IntConstant c1 = new IntConstant(7);
		IntConstant c2 = new IntConstant(1);
		IntConstant c3 = new IntConstant(9);

		Operation o1 = Operation.eq(v1, c1);
		Operation o2 = Operation.add(v1, c2);
		Operation o3 = Operation.eq(v2, o2);

		Operation o4 = Operation.and(o1, o3);
		Operation o5 = Operation.add(v2, c3);
		Operation o6 = Operation.le(v3, o5);
		Operation o = Operation.and(o4, o6);
		checkSat(o);
	}

	@Test
	public void test10() {
		// x = 7 & y = x + 1 & z <= y+9
		IntVariable v1 = new IntVariable("x", 0, 99);
		IntVariable v2 = new IntVariable("y", 0, 99);
		IntVariable v3 = new IntVariable("z", 0, 99);
		IntConstant c1 = new IntConstant(7);
		IntConstant c2 = new IntConstant(1);
		IntConstant c3 = new IntConstant(9);

		Operation o1 = Operation.eq(v1, c1);
		Operation o2 = Operation.add(v1, c2);
		Operation o3 = Operation.eq(v2, o2);
		Operation o4 = Operation.and(o1, o3);

		Operation o5 = Operation.add(v2, c3);
		Operation o6 = Operation.lt(v3, o5);
		Operation o = Operation.and(o4, o6);
		checkSat(o);
	}

	@Test
	public void test11() {
		int min = -100;
		int max = 1000;
		IntConstant const32768 = new IntConstant(-32768);
		IntConstant const0 = new IntConstant(0);
		IntConstant const8 = new IntConstant(8);
		IntConstant const16 = new IntConstant(16);
		IntConstant const48 = new IntConstant(48);
		IntConstant const65536 = new IntConstant(65536);
		IntVariable a1 = new IntVariable("a1", min, max);
		IntVariable c2 = new IntVariable("c2", min, max);

		Operation o1 = Operation.le(c2, const65536);
		Operation o2 = Operation.ge(c2, const32768);
		Operation o3 = Operation.and(o1, o2);

		Operation o4 = Operation.mul(a1, const8);
		Operation o40 = Operation.sub(const48, o4);
		Operation o400 = Operation.mod(o40, const16);
		Operation o5 = Operation.ne(o400, const0);

		Operation o = Operation.and(o5, o3);
		checkSat(o);
	}

	@Test
	public void unsatTest01() {
		IntVariable v1 = new IntVariable("x", 0, 99);
		IntConstant c1 = new IntConstant(10);
		Operation o1 = Operation.lt(v1, c1);
		Operation o2 = Operation.gt(v1, c1);

		Operation o = Operation.and(o1, o2);
		checkUnsat(o);
	}

	@Test
	public void unsatTest02() {
		IntVariable v1 = new IntVariable("x", 0, 99);
		IntConstant c1 = new IntConstant(0);
		Operation o1 = Operation.eq(v1, c1);
		Operation o2 = Operation.gt(v1, c1);
		Operation o = Operation.and(o1, o2);
		checkUnsat(o);
	}

	@Test
	public void unsatTest03() {
		IntVariable v1 = new IntVariable("x", 0, 99);
		IntConstant c1 = new IntConstant(0);
		Operation o1 = Operation.eq(v1, c1);
		Operation o2 = Operation.lt(v1, c1);
		Operation o3 = Operation.gt(v1, c1);
		Operation o4 = Operation.and(o1, o2);
		Operation o = Operation.and(o4, o3);
		checkUnsat(o);
	}

	// ======================================================================
	//
	// TEST SUPPORT ROUTINES
	//
	// ======================================================================

	private void checkSat(Expression expression) {
		Instance instance = new Instance(solver, null, expression);
		Object result = instance.request("sat");
		assertTrue(result instanceof ModelCore);
		assertTrue(((ModelCore) result).isSat());
	}

	private void checkUnsat(Expression expression) {
		Instance instance = new Instance(solver, null, expression);
		Object result = instance.request("sat");
		assertTrue(result instanceof ModelCore);
		assertFalse(((ModelCore) result).isSat());
	}
	
}
