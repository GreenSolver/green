/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.factorizer;

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
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.service.ModelService.Model;
import za.ac.sun.cs.green.util.Configuration;

/**
 * Complex tests for the model factorizer.
 */
public class ComplexModelFactorizerTest {

	/**
	 * The canonizer to use.  The other choice is just the identity service.
	 */
	private static final String CANONIZER = "za.ac.sun.cs.green.service.canonizer.ModelCanonizerService";
	// private static final String CANONIZER = "za.ac.sun.cs.green.service.identity.IdentityService";
	
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
		props.setProperty("green.services", "model");
		props.setProperty("green.service.model", "(bounder (factorizer (canonizer z3)))");
		props.setProperty("green.service.model.bounder", "za.ac.sun.cs.green.service.bounder.BounderService");
		props.setProperty("green.service.model.factorizer", "za.ac.sun.cs.green.service.factorizer.ModelFactorizerService");
		props.setProperty("green.service.model.canonizer", CANONIZER);
		props.setProperty("green.service.model.z3", "za.ac.sun.cs.green.service.z3.ModelZ3Service");
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
	 * <pre>
	 * (v0 <= v1) && (v1 <= v2) && ... && (vN-1 <= v0) && (vN < 10)
	 * (v0, v1, ..., vN in {0..99})
	 * </pre>
	 * 
	 * @result any model that satisfies the constraints
	 */
	@Test
	public void test01() {
		final int n = 10;
		final int top = 10;
		IntVariable[] v = new IntVariable[n + 1];
		for (int i = 0; i < n + 1; i++) {
			v[i] = new IntVariable("v" + i, 0, 99);
		}
		Operation[] o = new Operation[n + 1];
		for (int i = 0; i < n; i++) {
			o[i] = Operation.le(v[i], v[(i + 1) % n]);
		}
		IntConstant ctop = new IntConstant(top);
		o[n] = Operation.lt(v[n], ctop);
		Operation oo = o[0];
		for (int i = 1; i <= n; i++) {
			oo = Operation.and(oo, o[i]);
		}
		checkSat(oo, m -> {
			int prev = ((IntConstant) m.get(v[0])).getValue();
			for (int i = 1; i <= n; i++) {
				int next = ((IntConstant) m.get(v[i])).getValue();
				if (!(prev <= next)) {
					return false;
				}
				prev = next;
			}
			return prev <= 10;
		});
	}

	/**
	 * Check the following system of equations:
	 * 
	 * <pre>
	 * (v0 <= v1) && (v1 <= v2) && ... && (vN-1 <= v0) && (vN < 10) && (vN > 5)
	 * (v0, v1, ..., vN in {0..99})
	 * </pre> 
	 * 
	 * @result any model that satisfies the constraints
	 */
	@Test
	public void test01b() {
		final int n = 10;
		final int top = 10;
		IntVariable[] v = new IntVariable[n + 1];
		for (int i = 0; i < n + 1; i++) {
			v[i] = new IntVariable("v" + i, 0, 99);
		}
		Operation[] o = new Operation[n + 1];
		for (int i = 0; i < n; i++) {
			o[i] = Operation.le(v[i], v[(i + 1) % n]);
		}
		IntConstant ctop = new IntConstant(top);
		o[n] = Operation.lt(v[n], ctop);
		Operation oo = o[0];
		for (int i = 1; i <= n; i++) {
			oo = Operation.and(oo, o[i]);
		}
		IntConstant c5 = new IntConstant(5);
		Operation ooExtra = Operation.gt(v[n], c5);
		oo = Operation.and(oo, ooExtra);
		checkSat(oo, m -> {
			int prev = ((IntConstant) m.get(v[0])).getValue();
			int first = prev;
			for (int i = 1; i < n; i++) {
				int next = ((IntConstant) m.get(v[i])).getValue();
				if (!(prev <= next)) {
					return false;
				}
				prev = next;
			}
			int last = ((IntConstant) m.get(v[n])).getValue();
			return (prev <= first) && (last <= 10) && (last > 5);
		});
	}

	/**
	 * Check the following system of equations:
	 * 
	 * <pre>
	 * (v0 <= w0) && (w0 <= v0) && (v1 <= w1) && (w1 <= v1) && ... && (vN-1 <= wN-1)
	 * (v0, v1, ..., vN-1 in {0..99}) 
	 * (w0, w1, ..., wN-1 in {0..99}) 
	 * </pre>
	 * 
	 * @result any model that satisfies the constraints
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
		checkSat(oo, m -> {
			for (int i = 0; i < n; i++) {
				int vv = ((IntConstant) m.get(v[i])).getValue();
				int ww = ((IntConstant) m.get(w[i])).getValue();
				if (!(vv <= ww)) {
					return false;
				}
			}
			return true;
		});
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
	@SuppressWarnings("unused")
	private void checkUnsat(Expression expression) {
		Instance instance = new Instance(solver, null, expression);
		assertTrue(instance != null);
		Object result = instance.request("model");
		assertTrue(result instanceof Model);
		Model model = (Model) result;
		assertFalse(model.isSat());
	}

}
