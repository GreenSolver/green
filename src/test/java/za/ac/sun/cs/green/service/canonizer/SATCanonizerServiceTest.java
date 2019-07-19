/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.canonizer;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.Properties;
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
import za.ac.sun.cs.green.util.Configuration;

/**
 * Tests for {@link SATCanonizerService}.
 */
public class SATCanonizerServiceTest {

	/**
	 * Green server without the slicer service.
	 */
	public static Green solver1;

	/**
	 * Green server with the slicer service.
	 */
	public static Green solver2;

	/**
	 * Create and configure the two Green solvers, one with and one without the
	 * identity service.
	 */
	@BeforeClass
	public static void initialize() {
		solver1 = new Green("GREEN-TEST");
		Properties props1 = new Properties();
		props1.setProperty("green.services", "sat");
		props1.setProperty("green.service.sat", "(canonize sink)");
		props1.setProperty("green.service.sat.canonize", "za.ac.sun.cs.green.service.canonizer.SATCanonizerService");
		props1.setProperty("green.service.sat.sink", "za.ac.sun.cs.green.service.sink.SinkService");
		Configuration config1 = new Configuration(solver1, props1);
		config1.configure();
		solver2 = new Green("GREEN-TEST");
		Properties props2 = new Properties();
		props2.setProperty("green.services", "sat");
		props2.setProperty("green.service.sat", "(slice (canonize sink))");
		props2.setProperty("green.service.sat.slice", "za.ac.sun.cs.green.service.slicer.SATSlicerService");
		props2.setProperty("green.service.sat.canonize", "za.ac.sun.cs.green.service.canonizer.SATCanonizerService");
		props2.setProperty("green.service.sat.sink", "za.ac.sun.cs.green.service.sink.SinkService");
		Configuration config2 = new Configuration(solver2, props2);
		config2.configure();
	}

	// ======================================================================
	//
	// ACTUAL TESTS
	//
	// ======================================================================

	@Test
	public void test1_23() {
		IntVariable x5 = new IntVariable("x5", 0, 99);
		Operation o2b = Operation.ne(x5, x5);
		Operation o2a = Operation.not(o2b);
		check(solver1, o2a, "!(x5!=x5)", "0==0");
	}

	@Test
	public void test2_01() {
		IntVariable v = new IntVariable("aa", 0, 99);
		IntConstant c = new IntConstant(0);
		Operation o = Operation.eq(v, c);
		check(solver2, o, "aa==0", "1*v==0");
	}

	@Test
	public void test2_02() {
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntConstant c1 = new IntConstant(0);
		Operation o1 = Operation.eq(v1, c1);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		IntConstant c2 = new IntConstant(1);
		Operation o2 = Operation.ne(v2, c2);
		Operation o3 = Operation.and(o1, o2);
		check(solver2, o3, "(aa==0)&&(bb!=1)", "1*v==0", "1*v+-1!=0");
	}

	@Test
	public void test2_03() {
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntConstant c1 = new IntConstant(0);
		Operation o1 = Operation.eq(v1, c1);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		IntConstant c2 = new IntConstant(1);
		Operation o2 = Operation.ne(v2, c2);
		check(solver2, o1, o2, "(aa==0)&&(bb!=1)", "1*v==0");
	}

	@Test
	public void test2_04() {
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntConstant c1 = new IntConstant(0);
		Operation o1 = Operation.eq(v1, c1);
		IntConstant c2 = new IntConstant(1);
		Operation o2 = Operation.ne(v1, c2);
		check(solver2, o1, o2, "(aa==0)&&(aa!=1)", "1*v==0", "1*v+-1!=0");
	}

	@Test
	public void test2_05() {
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		Operation o1 = Operation.eq(v1, v2);
		IntVariable v3 = new IntVariable("cc", 0, 99);
		Operation o2 = Operation.eq(v2, v3);
		IntVariable v4 = new IntVariable("dd", 0, 99);
		Operation o3 = Operation.eq(v3, v4);
		IntVariable v5 = new IntVariable("ee", 0, 99);
		Operation o4 = Operation.eq(v4, v5);
		Operation o34 = Operation.and(o3, o4);
		Operation o234 = Operation.and(o2, o34);
		check(solver2, o1, o234, "(aa==bb)&&((bb==cc)&&((cc==dd)&&(dd==ee)))", "1*v+-1*v==0", "1*v+-1*v==0",
				"1*v+-1*v==0", "1*v+-1*v==0");
	}

	@Test
	public void test2_06() {
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		Operation o1 = Operation.eq(v1, v2);
		IntVariable v3 = new IntVariable("cc", 0, 99);
		Operation o2 = Operation.eq(v2, v3);
		IntVariable v4 = new IntVariable("dd", 0, 99);
		Operation o3 = Operation.eq(v3, v4);
		IntVariable v5 = new IntVariable("ee", 0, 99);
		IntVariable v6 = new IntVariable("ff", 0, 99);
		Operation o4 = Operation.eq(v5, v6);
		Operation o34 = Operation.and(o3, o4);
		Operation o234 = Operation.and(o2, o34);
		check(solver2, o1, o234, "(aa==bb)&&((bb==cc)&&((cc==dd)&&(ee==ff)))", "1*v+-1*v==0", "1*v+-1*v==0",
				"1*v+-1*v==0");
	}

	@Test
	public void test2_07() {
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		IntVariable v3 = new IntVariable("cc", 0, 99);
		IntVariable v4 = new IntVariable("dd", 0, 99);
		IntVariable v5 = new IntVariable("ee", 0, 99);
		IntVariable v6 = new IntVariable("ff", 0, 99);
		IntVariable v7 = new IntVariable("gg", 0, 99);
		Operation o1 = Operation.lt(v1, Operation.add(v2, v3));
		Operation o2 = Operation.lt(v2, Operation.add(v4, v5));
		Operation o3 = Operation.lt(v3, Operation.add(v6, v7));
		Operation o23 = Operation.and(o2, o3);
		check(solver2, o1, o23, "(aa<(bb+cc))&&((bb<(dd+ee))&&(cc<(ff+gg)))", "1*v+-1*v+-1*v+1<=0",
				"1*v+-1*v+-1*v+1<=0", "1*v+-1*v+-1*v+1<=0");
	}

	@Test
	public void test2_08() {
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		IntVariable v3 = new IntVariable("cc", 0, 99);
		IntVariable v4 = new IntVariable("dd", 0, 99);
		IntVariable v5 = new IntVariable("ee", 0, 99);
		IntVariable v6 = new IntVariable("ff", 0, 99);
		IntVariable v7 = new IntVariable("gg", 0, 99);
		IntVariable v8 = new IntVariable("hh", 0, 99);
		Operation o1 = Operation.lt(v1, Operation.add(v2, v3));
		Operation o2 = Operation.lt(v2, Operation.add(v4, v5));
		Operation o3 = Operation.lt(v6, Operation.add(v7, v8));
		Operation o23 = Operation.and(o2, o3);
		check(solver2, o1, o23, "(aa<(bb+cc))&&((bb<(dd+ee))&&(ff<(gg+hh)))", "1*v+-1*v+-1*v+1<=0",
				"1*v+-1*v+-1*v+1<=0");
	}

	@Test
	public void test2_09() {
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		IntVariable v3 = new IntVariable("cc", 0, 99);
		Operation o1 = Operation.add(v1, v2);
		Operation o2 = Operation.add(v1, v3);
		Operation o3 = Operation.lt(o1, o2);
		check(solver2, o3, "(aa+bb)<(aa+cc)", "1*v+-1*v+1<=0");
	}

	@Test
	public void test2_10() {
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		IntVariable v3 = new IntVariable("cc", 0, 99);
		Operation o1 = Operation.add(v1, v2);
		Operation o2 = Operation.sub(v1, v3);
		Operation o3 = Operation.lt(o1, o2);
		check(solver2, o3, "(aa+bb)<(aa-cc)", "1*v+1*v+1<=0");
	}

	@Test
	public void test2_11() {
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		Operation o1 = Operation.add(v1, v2);
		Operation o2 = Operation.sub(v2, v1);
		Operation o3 = Operation.lt(o1, o2);
		check(solver2, o3, "(aa+bb)<(bb-aa)", "2*v+1<=0");
	}

	@Test
	public void test2_12() {
		IntConstant c1 = new IntConstant(2);
		IntConstant c2 = new IntConstant(3);
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		Operation o1 = Operation.add(c1, c2);
		Operation o2 = Operation.mul(o1, v1);
		Operation o3 = Operation.lt(o2, v2);
		check(solver2, o3, "((2+3)*aa)<bb", "5*v+-1*v+1<=0");
	}

	@Test
	public void test2_13() {
		IntConstant c1 = new IntConstant(2);
		IntConstant c2 = new IntConstant(3);
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		Operation o1 = Operation.add(c1, c2);
		Operation o2 = Operation.mul(v1, o1);
		Operation o3 = Operation.lt(o2, v2);
		check(solver2, o3, "(aa*(2+3))<bb", "5*v+-1*v+1<=0");
	}

	@Test
	public void test2_14() {
		IntConstant c1 = new IntConstant(2);
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		Operation o1 = Operation.sub(v1, v2);
		Operation o2 = Operation.mul(o1, c1);
		Operation o3 = Operation.lt(o2, v1);
		check(solver2, o3, "((aa-bb)*2)<aa", "1*v+-2*v+1<=0");
	}

	@Test
	public void test2_15() {
		IntConstant c1 = new IntConstant(2);
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		Operation o1 = Operation.sub(v1, v2);
		Operation o2 = Operation.mul(c1, o1);
		Operation o3 = Operation.lt(o2, v1);
		check(solver2, o3, "(2*(aa-bb))<aa", "1*v+-2*v+1<=0");
	}

	@Test
	public void test2_16() {
		IntConstant c1 = new IntConstant(2);
		IntConstant c2 = new IntConstant(4);
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		Operation o1 = Operation.mul(v1, c1);
		Operation o2 = Operation.mul(c2, v1);
		Operation o3 = Operation.add(o1, o2);
		Operation o4 = Operation.lt(o3, v2);
		check(solver2, o4, "((aa*2)+(4*aa))<bb", "6*v+-1*v+1<=0");
	}

	@Test
	public void test2_17() {
		IntConstant c1 = new IntConstant(2);
		Operation o1 = Operation.lt(c1, c1);
		check(solver2, o1, "2<2", "0==1");
	}

	@Test
	public void test2_18() {
		IntConstant c1 = new IntConstant(2);
		IntVariable v1 = new IntVariable("aa", 0, 99);
		Operation o1 = Operation.lt(c1, c1);
		Operation o2 = Operation.lt(v1, c1);
		Operation o3 = Operation.and(o1, o2);
		check(solver2, o3, "(2<2)&&(aa<2)", "0==1");
	}

	@Test
	public void test2_19() {
		IntConstant c1 = new IntConstant(2);
		Operation o1 = Operation.le(c1, c1);
		check(solver2, o1, "2<=2", "0==0");
	}

	@Test
	public void test2_20() {
		IntConstant c1 = new IntConstant(2);
		IntVariable v1 = new IntVariable("aa", 0, 99);
		Operation o1 = Operation.le(c1, c1);
		Operation o2 = Operation.lt(v1, c1);
		Operation o3 = Operation.and(o1, o2);
		check(solver2, o3, "(2<=2)&&(aa<2)", "1*v+-1<=0");
	}

	// @Test
	public void test2_21() {
		IntVariable x1 = new IntVariable("x1", 0, 99);
		IntVariable x2 = new IntVariable("x2", 0, 99);
		IntVariable x3 = new IntVariable("x3", 0, 99);
		IntVariable x4 = new IntVariable("x4", 0, 99);
		IntVariable x5 = new IntVariable("x5", 0, 99);

		IntConstant c1 = new IntConstant(1);
		IntConstant c0 = new IntConstant(0);

		Operation x2eq1 = Operation.eq(x2, c1);
		Operation x1eq1 = Operation.eq(x1, c1);
		Operation c0eqc0 = Operation.eq(c0, c0);
		Operation o4a = Operation.and(x1eq1, c0eqc0);
		Operation o4b = Operation.and(x2eq1, o4a);

		Operation o1a = Operation.eq(x3, c1);
		Operation o1 = Operation.not(o1a);

		Operation o2a = Operation.eq(x5, x5);
		Operation o2 = Operation.le(x4, x5);
		Operation o3 = Operation.ne(x4, x5);
		Operation o3a = Operation.and(o3, o4b);

		Operation o4 = Operation.and(o2, o3a);

		Operation o5 = Operation.and(o2a, o4);
		Operation o6 = Operation.and(o1, o5);
		check(solver2, o6, "(!(x3==1))&&((x5==x5)&&((x4<=x5)&&((x4!=x5)&&((x2==1)&&((x1==1)&&(0==0))))))", "1*v+-1<=0");
	}

	@Test
	public void test2_23() {
		IntVariable x5 = new IntVariable("x5", 0, 99);
//		IntConstant c1 = new IntConstant(1);
//		IntConstant c0 = new IntConstant(0);
		Operation o2b = Operation.ne(x5, x5);
		Operation o2a = Operation.not(o2b);
		check(solver2, o2a, "!(x5!=x5)", "0==1");
	}

	// ======================================================================
	//
	// TEST SUPPORT ROUTINES
	//
	// ======================================================================

	private void finalCheck(String observed, String[] expected) {
		String s0 = observed.replaceAll("[()]", "");
		String s1 = s0.replaceAll("v[0-9]", "v");
		SortedSet<String> s2 = new TreeSet<String>(Arrays.asList(s1.split("&&")));
		SortedSet<String> s3 = new TreeSet<String>(Arrays.asList(expected));
		assertEquals(s2, s3);
	}

	private void check(Green solver, Expression expression, String fullExpected, String... expected) {
		Instance i = new Instance(solver, null, null, expression);
		Expression e = i.getExpression();
		assertTrue(e.equals(expression));
		assertEquals(expression.toString(), e.toString());
		assertEquals(fullExpected, i.getFullExpression().toString());
		Object result = i.request("sat");
		assertNotNull(result);
		assertEquals(Instance.class, result.getClass());
		Instance j = (Instance) result;
		finalCheck(j.getExpression().toString(), expected);
	}

	private void check(Green solver, Expression expression, Expression parentExpression, String fullExpected,
			String... expected) {
		Instance i1 = new Instance(solver, null, parentExpression);
		Instance i2 = new Instance(solver, i1, expression);
		Expression e = i2.getExpression();
		assertTrue(e.equals(expression));
		assertEquals(expression.toString(), e.toString());
		assertEquals(fullExpected, i2.getFullExpression().toString());
		Object result = i2.request("sat");
		assertNotNull(result);
		assertEquals(Instance.class, result.getClass());
		Instance j = (Instance) result;
		finalCheck(j.getExpression().toString(), expected);
	}

}
