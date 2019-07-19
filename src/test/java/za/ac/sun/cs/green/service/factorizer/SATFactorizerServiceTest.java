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
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Properties;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import org.junit.BeforeClass;
import org.junit.Test;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Operation.Operator;
import za.ac.sun.cs.green.service.sink.FactorSinkService;
import za.ac.sun.cs.green.util.Configuration;

/**
 * Tests for the SAT factorizer.
 */
public class SATFactorizerServiceTest {

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
		props.setProperty("green.service.sat", "(factor sink)");
		props.setProperty("green.service.sat.factor", "za.ac.sun.cs.green.service.factorizer.SATFactorizerService");
		props.setProperty("green.service.sat.sink", "za.ac.sun.cs.green.service.sink.FactorSinkService");
		Configuration config = new Configuration(solver, props);
		config.configure();
	}

	// ======================================================================
	//
	// ACTUAL TESTS
	//
	// ======================================================================

	/**
	 * Check a trivial example without variables.
	 *
	 * <pre>
	 * 2 == 2
	 * </pre>
	 * 
	 * @result <code>2==2</code>
	 */
	@Test
	public void test00() {
		IntConstant c1 = new IntConstant(2);
		IntConstant c2 = new IntConstant(2);
		Operation o = Operation.eq(c1, c2);
		check(o, setof(o));
	}

	/**
	 * Check a trivial example with a single conjunct.
	 *
	 * <pre>
	 * v == 0
	 * </pre>
	 * 
	 * @result <code>v==0</code>
	 */
	@Test
	public void test01() {
		IntVariable v = new IntVariable("v", 0, 99);
		IntConstant c = new IntConstant(0);
		Operation o = Operation.eq(v, c);
		check(o, setof(o));
	}

	/**
	 * Check an example with two independent conjuncts.
	 *
	 * <pre>
	 * (v1 == 42) && (v2 != 1)
	 * </pre>
	 * 
	 * @result <code>v1==42</code> and <code>v2!=1</code>
	 */
	@Test
	public void test02() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntConstant c1 = new IntConstant(42);
		Operation o1 = Operation.eq(v1, c1);
		IntVariable v2 = new IntVariable("v2", 0, 99);
		IntConstant c2 = new IntConstant(1);
		Operation o2 = Operation.ne(v2, c2);
		Operation o3 = Operation.and(o2, o1);
		check(o3, setof(o1), setof(o2));
	}

	/**
	 * Check an example with two dependent conjuncts.
	 *
	 * <pre>
	 * (v1 == 0) && (v1 != 1)
	 * </pre>
	 * 
	 * @result <code>(v1==0)&&(v1!=1)</code>
	 */
	@Test
	public void test03() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntConstant c1 = new IntConstant(0);
		Operation o1 = Operation.eq(v1, c1);
		IntConstant c2 = new IntConstant(1);
		Operation o2 = Operation.ne(v1, c2);
		Operation o3 = Operation.and(o2, o1);
		check(o3, setof(o1, o2));
	}

	/**
	 * Check an example with two dependent conjuncts (unsatisfiable).
	 *
	 * <pre>
	 * (v1 == 0) && (v1 == 1)
	 * </pre>
	 * 
	 * @result <code>(v1==0)&&(v1!=1)</code>
	 */
	@Test
	public void test03a() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntConstant c1 = new IntConstant(0);
		Operation o1 = Operation.eq(v1, c1);
		IntConstant c2 = new IntConstant(1);
		Operation o2 = Operation.eq(v1, c2);
		Operation o3 = Operation.and(o2, o1);
		check(o3, setof(o1, o2));
	}
	
	/**
	 * Check an example with three chained dependent conjuncts.
	 *
	 * <pre>
	 * (v2 == v3) && ((v3 == v4) && (v4 == v5))
	 * </pre>
	 * 
	 * @result <code>(v2==v3)&&(v3==v4)&&(v4==v5)</code>
	 */
	@Test
	public void test04() {
		IntVariable v2 = new IntVariable("v2", 0, 99);
		IntVariable v3 = new IntVariable("v3", 0, 99);
		Operation o2 = Operation.eq(v2, v3);
		IntVariable v4 = new IntVariable("v4", 0, 99);
		Operation o3 = Operation.eq(v3, v4);
		IntVariable v5 = new IntVariable("v5", 0, 99);
		Operation o4 = Operation.eq(v4, v5);
		Operation o34 = Operation.and(o3, o4);
		Operation o234 = Operation.and(o2, o34);
		check(o234, setof(o2, o3, o4));
	}

	/**
	 * Check an example with two pairs of independent conjuncts.
	 *
	 * <pre>
	 * (v1 == v2) && ((v6 == v4) && ((v5 == v6) && (v2 == v3)))
	 * </pre>
	 * 
	 * @result <code>(v1==v2)&&(v2==v3)</code> and <code>(v6==v4)&&(v5==v6)</code>
	 */
	@Test
	public void test05() {
		IntVariable v1 = new IntVariable("v1", 0, 99);
		IntVariable v2 = new IntVariable("v2", 0, 99);
		IntVariable v3 = new IntVariable("v3", 0, 99);
		Operation o1 = Operation.eq(v1, v2);
		Operation o2 = Operation.eq(v2, v3);
		IntVariable v4 = new IntVariable("v4", 0, 99);
		IntVariable v5 = new IntVariable("v5", 0, 99);
		IntVariable v6 = new IntVariable("v6", 0, 99);
		Operation o3 = Operation.eq(v6, v4);
		Operation o4 = Operation.eq(v5, v6);
		Operation o34 = Operation.and(o4, o2);
		Operation o234 = Operation.and(o3, o34);
		Operation o1234 = Operation.and(o1, o234);
		check(o1234, setof(o1, o2), setof(o3, o4));
	}

	/**
	 * Check an example with three dependent complex conjuncts.
	 *
	 * <pre>
	 * ((v1 < v2 + v3) && (v2 < v4 + v5)) && (v3 < v6 + v7)
	 * </pre>
	 * 
	 * @result <code>(v1<v2+v3)&&(v2<v4+v5)&&(v3<v6+v7)</code>
	 */
	@Test
	public void test06() {
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
		Operation o12 = Operation.and(o1, o2);
		Operation o123 = Operation.and(o12, o3);
		check(o123, setof(o1, o2, o3));
	}

	/**
	 * Check an example with three complex conjuncts, two are dependent.
	 *
	 * <pre>
	 * ((v1 < v2 + v3) && (v2 < v4 + v5)) && (v6 < v7 + v8)
	 * </pre>
	 * 
	 * @result <code>(v1<v2+v3)&&(v2<v4+v5)</code> and <code>v3<v6+v7</code>
	 */
	@Test
	public void test07() {
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
		Operation o12 = Operation.and(o1, o2);
		Operation o123 = Operation.and(o12, o3);
		check(o123, setof(o1, o2), setof(o3));
	}

	// ======================================================================
	//
	// TEST SUPPORT ROUTINES
	//
	// ======================================================================

	/**
	 * Create a set containing the given elements.
	 *
	 * @param expressions array of elements
	 * @return a {@link HashSet} with the elements
	 */
	@SafeVarargs
	private final <T> Set<T> setof(T... expressions) {
		return new HashSet<T>(Arrays.asList(expressions));
	}

	/**
	 * Factorize the given expression and check that the factors are what we expect.
	 *
	 * @param expression expression to factorize
	 * @param factors    expected factors
	 */
	@SafeVarargs
	private final void check(Expression expression, Set<Expression>... factors) {
		int n = factors.length;
		Instance instance = new Instance(solver, null, expression);
		Expression expr = instance.getExpression();
		assertEquals(expression, expr);
		assertEquals(expression.toString(), expr.toString());
		Object satResult = instance.request("sat");
		assertNull(satResult);
		Object collectedFactors = instance.getData(FactorSinkService.class);
		assertTrue(collectedFactors instanceof Set<?>);
		@SuppressWarnings("unchecked")
		Set<Expression> result = (Set<Expression>) collectedFactors;
		assertEquals(n, result.size());
		String[] actual = new String[n];
		for (int i = 0; i < n; i++) {
			actual[i] = cleanup(factors[i]);
		}
		String[] expected = new String[n];
		int j = 0;
		for (Expression factor : result) {
			expected[j++] = cleanup(factor);
		}
		Arrays.sort(actual);
		Arrays.sort(expected);
		for (int i = 0; i < n; i++) {
			assertEquals(expected[i], actual[i]);
		}
	}

	/**
	 * Recursively construct a set of conjuncts from a factor expression
	 *
	 * @param factor expression to disassemble
	 * @return set of conjuncts of expressions
	 */
	private Set<Expression> collect(Expression factor) {
		if (factor instanceof Operation) {
			Operation operation = (Operation) factor;
			if (operation.getOperator() == Operator.AND) {
				Set<Expression> factors = collect(operation.getOperand(0));
				factors.addAll(collect(operation.getOperand(1)));
				return factors;
			}
		}
		return setof(factor);
	}

	/**
	 * Reassemble a factor as a string after breaking it into conjuncts.
	 *
	 * @param factor expression to disassemble and reassemble
	 * @return conjuncts of the parameter separated with ";;"
	 */
	private String cleanup(Expression factor) {
		return cleanup(collect(factor));
	}

	/**
	 * Reassemble a set of expressions by converting them to strings, sorting the
	 * strings, and concatenating the results, separated by ";;".
	 *
	 * @param factors set of expressions
	 * @return conjuncts of the parameter separated with ";;"
	 */
	private String cleanup(Set<Expression> factors) {
		SortedSet<String> sorted = new TreeSet<>();
		for (Expression factor : factors) {
			sorted.add(factor.toString());
		}
		return String.join(";;", sorted);
	}

}
