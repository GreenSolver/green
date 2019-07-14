/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.factorizer;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import org.junit.BeforeClass;
import org.junit.Test;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Operation.Operator;

/**
 * Tests for the factorizer.
 */
public class FactorizerTest {

	/**
	 * The instance of the factorizer used throughout the test.
	 */
	public static Factorizer factorizer;

	/**
	 * Create an instance of the factorizer.
	 */
	@BeforeClass
	public static void initialize() {
		Green solver = new Green("GREEN-TEST");
		factorizer = new Factorizer(solver.getLogger());
	}

	// ======================================================================
	//
	// ACTUAL TESTS
	//
	// ======================================================================

	/**
	 * Check a trivial example without an "and".
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
		IntConstant c0 = new IntConstant(0);
		Operation o = new Operation(Operation.Operator.EQ, v, c0);
		check(o, setof(o));
	}

	/**
	 * Check an easy example with an "and" but with only a single factor.
	 *
	 * <pre>
	 * (v == 0) && (v < 10)
	 * </pre>
	 * 
	 * @result <code>(v==0)&&(v<10)</code>
	 */
	@Test
	public void test02() {
		IntVariable v = new IntVariable("v", 0, 99);
		IntConstant c0 = new IntConstant(0);
		IntConstant c10 = new IntConstant(10);
		Operation o1 = new Operation(Operation.Operator.EQ, v, c0);
		Operation o2 = new Operation(Operation.Operator.LT, v, c10);
		Operation o = new Operation(Operation.Operator.AND, o1, o2);
		check(o, setof(o1, o2));
	}

	/**
	 * Check an easy example with an "and" but with only a single factor.
	 *
	 * <pre>
	 * (v == 0) && (w > v)
	 * </pre>
	 * 
	 * @result <code>(v==0)&&(w>v)</code>
	 */
	@Test
	public void test03() {
		IntVariable v = new IntVariable("v", 0, 99);
		IntVariable w = new IntVariable("w", 0, 99);
		IntConstant c0 = new IntConstant(0);
		Operation o1 = new Operation(Operation.Operator.EQ, v, c0);
		Operation o2 = new Operation(Operation.Operator.GT, w, v);
		Operation o = new Operation(Operation.Operator.AND, o1, o2);
		check(o, setof(o1, o2));
	}

	/**
	 * Check an easy example with an "and" and two factors.
	 *
	 * <pre>
	 * (v == 0) && (w > 0)
	 * </pre>
	 * 
	 * @result <code>(v==0)</code> and <code>(w>0)</code>
	 */
	@Test
	public void test04() {
		IntVariable v = new IntVariable("v", 0, 99);
		IntVariable w = new IntVariable("w", 0, 99);
		IntConstant c0 = new IntConstant(0);
		Operation o1 = new Operation(Operation.Operator.EQ, v, c0);
		Operation o2 = new Operation(Operation.Operator.GT, w, c0);
		Operation o = new Operation(Operation.Operator.AND, o1, o2);
		check(o, setof(o1), setof(o2));
	}

	/**
	 * Check an example with a chain of variables.
	 *
	 * <pre>
	 * (a > b) && (b > c) && (c > d) && (d > e)
	 * </pre>
	 * 
	 * @result <code>(a>b)&&(b>c)&&(c>d)&&(d>e)</code>
	 */
	@Test
	public void test05() {
		IntVariable a = new IntVariable("a", 0, 99);
		IntVariable b = new IntVariable("b", 0, 99);
		IntVariable c = new IntVariable("c", 0, 99);
		IntVariable d = new IntVariable("d", 0, 99);
		IntVariable e = new IntVariable("e", 0, 99);
		Operation o1 = new Operation(Operation.Operator.GT, a, b);
		Operation o2 = new Operation(Operation.Operator.GT, b, c);
		Operation o3 = new Operation(Operation.Operator.GT, c, d);
		Operation o4 = new Operation(Operation.Operator.GT, d, e);
		Operation o34 = new Operation(Operation.Operator.AND, o3, o4);
		Operation o234 = new Operation(Operation.Operator.AND, o2, o34);
		Operation o = new Operation(Operation.Operator.AND, o1, o234);
		check(o, setof(o1, o2, o3, o4));
	}

	/**
	 * Check an example with a chain of variables. Different from a similar test but
	 * with conjuncts in a different order.
	 *
	 * <pre>
	 * (a > b) && (b > c) && (c > d) && (d > e)
	 * </pre>
	 * 
	 * @result <code>(a>b)&&(b>c)&&(c>d)&&(d>e)</code>
	 */
	@Test
	public void test05a() {
		IntVariable a = new IntVariable("a", 0, 99);
		IntVariable b = new IntVariable("b", 0, 99);
		IntVariable c = new IntVariable("c", 0, 99);
		IntVariable d = new IntVariable("d", 0, 99);
		IntVariable e = new IntVariable("e", 0, 99);
		Operation o1 = new Operation(Operation.Operator.GT, d, e);
		Operation o2 = new Operation(Operation.Operator.GT, c, d);
		Operation o3 = new Operation(Operation.Operator.GT, b, c);
		Operation o4 = new Operation(Operation.Operator.GT, a, b);
		Operation o34 = new Operation(Operation.Operator.AND, o3, o4);
		Operation o234 = new Operation(Operation.Operator.AND, o2, o34);
		Operation o = new Operation(Operation.Operator.AND, o1, o234);
		check(o, setof(o1, o2, o3, o4));
	}

	/**
	 * Check an example with an "and" nested inside an "or".  But there is a dependency between the conjuncts of the top-level "and". 
	 *
	 * <pre>
	 * (a > b) && ((b > c) || ((c > d) && (d > e)))
	 * </pre>
	 * 
	 * @result <code>(a>b)&&((b>c)||((c>d)&&(d>e)))</code>
	 */
	@Test
	public void test06() {
		IntVariable a = new IntVariable("a", 0, 99);
		IntVariable b = new IntVariable("b", 0, 99);
		IntVariable c = new IntVariable("c", 0, 99);
		IntVariable d = new IntVariable("d", 0, 99);
		IntVariable e = new IntVariable("e", 0, 99);
		Operation o1 = new Operation(Operation.Operator.GT, a, b);
		Operation o2 = new Operation(Operation.Operator.GT, b, c);
		Operation o3 = new Operation(Operation.Operator.GT, c, d);
		Operation o4 = new Operation(Operation.Operator.GT, d, e);
		Operation o34 = new Operation(Operation.Operator.AND, o3, o4);
		Operation o234 = new Operation(Operation.Operator.OR, o2, o34);
		Operation o = new Operation(Operation.Operator.AND, o1, o234);
		check(o, setof(o1, o234));
	}

	/**
	 * Check an example with an "and" nested inside an "or".  There is a dependency between the conjuncts of the top-level "and". 
	 *
	 * <pre>
	 * (a > 0) && ((b > c) || ((c > d) && (d > e)))
	 * </pre>
	 * 
	 * @result <code>(a>0)</code> and <code>(b>c)||((c>d)&&(d>e))</code>
	 */
	@Test
	public void test06a() {
		IntVariable a = new IntVariable("a", 0, 99);
		IntVariable b = new IntVariable("b", 0, 99);
		IntVariable c = new IntVariable("c", 0, 99);
		IntVariable d = new IntVariable("d", 0, 99);
		IntVariable e = new IntVariable("e", 0, 99);
		IntConstant c0 = new IntConstant(0);
		Operation o1 = new Operation(Operation.Operator.GT, a, c0);
		Operation o2 = new Operation(Operation.Operator.GT, b, c);
		Operation o3 = new Operation(Operation.Operator.GT, c, d);
		Operation o4 = new Operation(Operation.Operator.GT, d, e);
		Operation o34 = new Operation(Operation.Operator.AND, o3, o4);
		Operation o234 = new Operation(Operation.Operator.OR, o2, o34);
		Operation o = new Operation(Operation.Operator.AND, o1, o234);
		check(o, setof(o1), setof(o234));
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
		Set<Expression> result = factorizer.factorize(expression);
		assertNotNull(result);
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
