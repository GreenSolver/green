/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.z3;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Map;
import java.util.Properties;
import java.util.function.Function;

import org.junit.BeforeClass;
import org.junit.Test;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.service.ModelService.Model;
import za.ac.sun.cs.green.expr.RealConstant;
import za.ac.sun.cs.green.expr.RealVariable;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.util.Configuration;

/**
 * Tests for {@link ModelZ3Service} with real constraints.
 */
public class ModelZ3RealServiceTest {

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
		props.setProperty("green.services", "model");
		props.setProperty("green.service.model", "z3");
		props.setProperty("green.service.model.z3", "za.ac.sun.cs.green.service.z3.ModelZ3RealService");
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
	 * (v in {-99.0..99.0}) && (v <= -0.5)
	 * </pre>
	 *
	 * @result any model that satisfies the constraints
	 */
	@Test
	public void test01() {
		RealVariable v = new RealVariable("v", -99.0, 99.0);
		RealConstant cm0x5 = new RealConstant(-0.5);
		Operation o = Operation.le(v, cm0x5);
		checkSat(o, m -> {
			double w = ((RealConstant) m.get(v)).getValue();
			return (w >= -99) && (w <= 99) && (w <= -0.5);
		});
	}

	/**
	 * Check:
	 * 
	 * <pre>
	 * (v in {-99..99}) && (v <= 20)
	 * </pre>
	 *
	 * @result any model that satisfies the constraints
	 */
	@Test
	public void test02() {
		IntVariable v = new IntVariable("v", -99, 99);
		IntConstant c20 = new IntConstant(20);
		Operation o = Operation.le(v, c20);
		checkSat(o, m -> {
			int w = ((IntConstant) m.get(v)).getValue();
			return (w >= -99) && (w <= 99) && (w <= 20);
		});
	}

	/**
	 * Check:
	 * 
	 * <pre>
	 * (v1 in {0..50}) && (v2 in {0.0..50.0}) &&
	 * (v2 > 25.5) && (v1 < 2) && (v1 != v2)
	 * </pre>
	 *
	 * @result any model that satisfies the constraints
	 */
	@Test
	public void test03() {
		IntVariable v1 = new IntVariable("v1", 0, 50);
		IntConstant c2 = new IntConstant(2);
		RealVariable v2 = new RealVariable("v2", 0.0, 50.0);
		RealConstant c25x5 = new RealConstant(25.5);
		Operation t1 = Operation.gt(v2, c25x5);
		Operation t2 = Operation.lt(v1, c2);
		Operation t3 = Operation.ne(v1, v2);
		Operation o = Operation.and(Operation.and(t1, t2), t3);
		checkSat(o, m -> {
			int w1 = ((IntConstant) m.get(v1)).getValue();
			double w2 = ((RealConstant) m.get(v2)).getValue();
			boolean b1 = (w1 >= 0) && (w1 <= 50);
			boolean b2 = (w2 >= 0.0) && (w2 <= 50.0);
			boolean q0 = (w2 > 25.5);
			boolean q1 = (w1 < 2);
			boolean q2 = (w1 != w2);
			return b1 && b2 && q0 && q1 && q2;
		});
	}

	/**
	 * Check:
	 * 
	 * <pre>
	 * (v in {0..2}) && (v > 1) && (v < 1.5)
	 * </pre>
	 *
	 * @result expression is unsatisfiable
	 */
	@Test
	public void test04() {
		IntVariable v = new IntVariable("v", 0, 2);
		IntConstant c1 = new IntConstant(1);
		RealConstant c1x5 = new RealConstant(1.5);
		Operation o1 = Operation.gt(v, c1);
		Operation o2 = Operation.lt(v, c1x5);
		Operation o = Operation.and(o1, o2);
		checkUnsat(o);
	}

	// ======================================================================
	//
	// TEST SUPPORT ROUTINES
	//
	// ======================================================================

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
		Object result = instance.request("model");
		assertTrue(result instanceof Model);
		Model model = (Model) result;
		assertTrue(model.isSat());
		assertTrue(checker.apply(model.getModel()));
	}

	/**
	 * Check that an expression is unsatisfiable.
	 *
	 * @param expression expression to solve
	 */
	private void checkUnsat(Expression expression) {
		Instance instance = new Instance(solver, null, expression);
		assertTrue(instance != null);
		Object result = instance.request("model");
		assertTrue(result instanceof Model);
		Model model = (Model) result;
		assertFalse(model.isSat());
	}
	
}
