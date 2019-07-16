/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.parser.sexpr;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import za.ac.sun.cs.green.expr.Operation;

/**
 * Tests for {@code LIAParser}.
 */
public class LIAParserTest {

	// ======================================================================
	//
	// ACTUAL TESTS
	//
	// ======================================================================

	@Test
	public void test01() {
		String inp = "1 1 lt v 0 c 0";
		String exp = "x0<0";
		check(inp, exp);
	}

	@Test
	public void test02() {
		String inp = "1 1 le v 0 c 0";
		String exp = "x0<=0";
		check(inp, exp);
	}

	@Test
	public void test03() {
		String inp = "1 1 gt v 0 c 0";
		String exp = "x0>0";
		check(inp, exp);
	}

	@Test
	public void test04() {
		String inp = "1 1 ge v 0 c 0";
		String exp = "x0>=0";
		check(inp, exp);
	}

	@Test
	public void test05() {
		String inp = "1 1 eq v 0 c 0";
		String exp = "x0==0";
		check(inp, exp);
	}

	@Test
	public void test06() {
		String inp = "1 1 ne v 0 c 0";
		String exp = "x0!=0";
		check(inp, exp);
	}

	@Test
	public void test07() {
		String inp = "1 1 ne * 2 v 0 v 0 c 0";
		String exp = "(x0*x0)!=0";
		check(inp, exp);
	}

	@Test
	public void test08() {
		String inp = "1 1 ne * 2 + 2 v 1 c 5 + 2 v 0 c 10 + 2 * 2 v 1 c 5 * 2 v 0 c 10";
		String exp = "((x1+5)*(x0+10))!=((x1*5)+(x0*10))";
		check(inp, exp);
	}

	@Test
	public void test09() {
		String inp = "1 1 ne * 3 v 0 v 1 v 2 v 3";
		String exp = "((x0*x1)*x2)!=x3";
		check(inp, exp);
	}

	@Test
	public void test10() {
		String inp = "2 2 lt v 0 c 0 lt v 0 c 1 1 gt v 0 c 0";
		String exp = "((x0<0)||(x0<1))&&(x0>0)";
		check(inp, exp);
	}

	// ======================================================================
	//
	// TEST SUPPORT ROUTINES
	//
	// ======================================================================

	/**
	 * Check that the input is corrected parsed.
	 *
	 * @param input    input for the parser
	 * @param expected correct output
	 */
	private void check(String input, String expected) {
		LIAParser parser = new LIAParser();
		Operation output = null;
		try {
			output = parser.parse(input);
		} catch (Exception e) {
			e.printStackTrace();
		}
		assertTrue(((output.toString()).equals(expected)));
	}

}
