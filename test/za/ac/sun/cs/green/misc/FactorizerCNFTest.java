package za.ac.sun.cs.green.misc;

import static org.junit.Assert.*;

import java.util.Arrays;
import java.util.Properties;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import org.junit.AfterClass;
import org.junit.Assume;
import org.junit.BeforeClass;
import org.junit.Test;

import za.ac.sun.cs.green.EntireSuite;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.service.sink.FactorSinkService;
import za.ac.sun.cs.green.util.Configuration;

public class FactorizerCNFTest {

	public static Green solver;

	@BeforeClass
	public static void initialize() {
		solver = new Green();
		Properties props = new Properties();
		props.setProperty("green.services", "sat");
		props.setProperty("green.service.sat","(factor sink)");
		props.setProperty("green.service.sat.factor",
				"za.ac.sun.cs.green.service.factorizer.SATFactorizerService");
		props.setProperty("green.service.sat.sink", "za.ac.sun.cs.green.service.sink.FactorSinkService");
		Configuration config = new Configuration(solver, props);
		config.configure();
	}

	@AfterClass
	public static void report() {
		if (solver != null) {
			solver.report();
		}
	}

	private boolean finalCheck(String[] expected, Instance factor) {
		String[] expectedReplaced = new String[expected.length];
		for (int i=0; i<expected.length; i++) {
			expectedReplaced[i] = expected[i].replaceAll("[()]", "");
		}
		String s0 = factor.getExpression().toString().replaceAll("[()]", "");
		SortedSet<String> s2 = new TreeSet<String>(Arrays.asList(s0.split("&&")));
		SortedSet<String> s3 = new TreeSet<String>(Arrays.asList(expectedReplaced));
		return s2.equals(s3);
	}
	
	private void finalCheck(String[][] expected, Set<Instance> factors) {
		assertEquals(expected.length, factors.size());
		for (Instance i : factors) {
			boolean found = false;
			for (String[] e : expected) {
				if (finalCheck(e, i)) {
					found = true;
					break;
				}
			}
			if (!found) {
				System.out.println("Not found: " + i.getExpression());
			}
			assertTrue(found);
		}
	}

	private void check(Expression expression, String[]... expected) {
		Instance i = new Instance(solver, null, expression);
		Expression e = i.getExpression();
		assertTrue(e.equals(expression));
		assertEquals(expression.toString(), e.toString());
		Object result = i.request("sat");
		assertEquals(null, result);
		Object f0 = i.getData(FactorSinkService.class);
		assertTrue(f0 instanceof Set<?>);
		@SuppressWarnings("unchecked")
		Set<Instance> f = (Set<Instance>) f0;
		finalCheck(expected, f);
	}

	private Operation BOOL(IntVariable v) {
		return new Operation(Operation.Operator.NE, v, Operation.ZERO);
	}

	/* (v1 or v2) and (v3 or v4) */
	
	@Test
	public void test1() {
		Operation v1 = BOOL(new IntVariable("a1", 0, 1));
		Operation v2 = BOOL(new IntVariable("a2", 0, 1));
		Operation v3 = BOOL(new IntVariable("a3", 0, 1));
		Operation v4 = BOOL(new IntVariable("a4", 0, 1));

		
		Operation c1 = new Operation(Operation.Operator.OR, v1, v2);
		Operation c2 = new Operation(Operation.Operator.OR, v3, v4);
		
		Operation all = new Operation(Operation.Operator.AND, c1, c2);
		
		check(all,new String[] { "(a1!=0)||(a2!=0)" }, new String[] { "(a3!=0)||(a4!=0)" });
		
	}	

	@Test
	public void test01() {
		Operation v1 = BOOL(new IntVariable("a1", 0, 1));
		Operation v2 = BOOL(new IntVariable("a2", 0, 1));
		Operation v3 = BOOL(new IntVariable("a3", 0, 1));
		Operation v4 = BOOL(new IntVariable("a4", 0, 1));

		Operation c1 = new Operation(Operation.Operator.OR, v1, v2);
		Operation c2 = new Operation(Operation.Operator.OR, c1, v3);
		
		Operation all = new Operation(Operation.Operator.AND, c2, v4);
		
		check(all,new String[] { "((a1!=0)||(a2!=0))||(a3!=0)" }, new String[] { "a4!=0" });
	}	

	
	@Test
	public void test2() {
		Operation v1 = BOOL(new IntVariable("a1", 0, 1));
		Operation v2 = BOOL(new IntVariable("a2", 0, 1));
		Operation v3 = BOOL(new IntVariable("a3", 0, 1));
		Operation v4 = BOOL(new IntVariable("a4", 0, 1));

		
		Operation c1 = new Operation(Operation.Operator.OR, v1, v2);
		Operation c2 = new Operation(Operation.Operator.OR, v2, v4);
		
		Operation all = new Operation(Operation.Operator.AND, c1, c2);
		
		check(all,new String[] { "((a1!=0)||(a2!=0))", "((a2!=0)||(a4!=0))" });
	}	

	@Test
	public void test3() {
		Operation v1 = BOOL(new IntVariable("a1", 0, 1));
		Operation v2 = BOOL(new IntVariable("a2", 0, 1));
		Operation v3 = BOOL(new IntVariable("a3", 0, 1));
		Operation v4 = BOOL(new IntVariable("a4", 0, 1));
		Operation v5 = BOOL(new IntVariable("a5", 0, 1));
		Operation v6 = BOOL(new IntVariable("a6", 0, 1));
		
		Operation c1 = new Operation(Operation.Operator.OR, v1, v2);
		Operation c2 = new Operation(Operation.Operator.OR, v3, v4);
		Operation c3 = new Operation(Operation.Operator.OR, v5, v6);
		
		Operation all1 = new Operation(Operation.Operator.AND, c1, c2);
		
		Operation all = new Operation(Operation.Operator.AND, all1, c3);
		check(all,new String[] { "(a1!=0)||(a2!=0)" }, new String[] { "(a3!=0)||(a4!=0)"}, new String[] { "(a5!=0)||(a6!=0)" });
	}	
	
		
}
