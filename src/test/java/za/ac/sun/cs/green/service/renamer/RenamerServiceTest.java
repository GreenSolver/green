package za.ac.sun.cs.green.service.renamer;

import org.junit.BeforeClass;
import org.junit.Test;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.util.Configuration;

import java.util.Arrays;
import java.util.Properties;
import java.util.SortedSet;
import java.util.TreeSet;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

public class RenamerServiceTest {

	public static Green solver;

	@BeforeClass
	public static void initialize() {
		solver = new Green("GREEN-TEST");
		Properties props1 = new Properties();
		props1.setProperty("green.services", "sat");
		props1.setProperty("green.service.sat", "(rename sink)");
		props1.setProperty("green.service.sat.rename", "za.ac.sun.cs.green.service.renamer.RenamerService");
		props1.setProperty("green.service.sat.sink", "za.ac.sun.cs.green.service.sink.SinkService");
		Configuration config1 = new Configuration(solver, props1);
		config1.configure();
	}

	private void finalCheck(String observed, String[] expected) {
		String s0 = observed.replaceAll("[()]", "");
//        String s1 = s0.replaceAll("v[0-9]", "v");
		SortedSet<String> s2 = new TreeSet<String>(Arrays.asList(s0.split("&&")));
		SortedSet<String> s3 = new TreeSet<String>(Arrays.asList(expected));
		assertEquals(s2, s3);
	}

	private void check(Green solver, Expression expression, String full, String... expected) {
		Instance i = new Instance(solver, null, null, expression);
		Expression e = i.getExpression();
		assertTrue(e.equals(expression));
		assertEquals(expression.toString(), e.toString());
		assertEquals(full, i.getFullExpression().toString());
		Object result = i.request("sat");
		assertNotNull(result);
		assertEquals(Instance.class, result.getClass());
		Instance j = (Instance) result;
		finalCheck(j.getExpression().toString(), expected);
	}

	private void check(Green solver, Expression expression, Expression parentExpression, String full,
			String... expected) {
		Instance i1 = new Instance(solver, null, parentExpression);
		Instance i2 = new Instance(solver, i1, expression);
		Expression e = i2.getExpression();
		assertTrue(e.equals(expression));
		assertEquals(expression.toString(), e.toString());
		assertEquals(full, i2.getFullExpression().toString());
		Object result = i2.request("sat");
		assertNotNull(result);
		assertEquals(Instance.class, result.getClass());
		Instance j = (Instance) result;
		finalCheck(j.getExpression().toString(), expected);
	}

	@Test
	public void test_01() {
		IntVariable v = new IntVariable("aa", 0, 99);
		IntConstant c = new IntConstant(0);
		Operation o = new Operation(Operation.Operator.EQ, v, c);
		check(solver, o, "aa==0", "v0==0");
	}

	@Test
	public void test_02() {
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntConstant c1 = new IntConstant(0);
		Operation o1 = new Operation(Operation.Operator.EQ, v1, c1);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		IntConstant c2 = new IntConstant(1);
		Operation o2 = new Operation(Operation.Operator.NE, v2, c2);
		Operation o3 = new Operation(Operation.Operator.AND, o1, o2);
		check(solver, o3, "(aa==0)&&(bb!=1)", "v0==0", "v1!=1");
	}

	@Test
	public void test_03() {
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntConstant c1 = new IntConstant(0);
		Operation o1 = new Operation(Operation.Operator.EQ, v1, c1);
		IntConstant c2 = new IntConstant(1);
		Operation o2 = new Operation(Operation.Operator.NE, v1, c2);
		check(solver, o1, o2, "(aa==0)&&(aa!=1)", "v0==0", "v0!=1");
	}

	@Test
	public void test_04() {
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		Operation o1 = new Operation(Operation.Operator.EQ, v1, v2);
		IntVariable v3 = new IntVariable("cc", 0, 99);
		Operation o2 = new Operation(Operation.Operator.EQ, v2, v3);
		IntVariable v4 = new IntVariable("dd", 0, 99);
		Operation o3 = new Operation(Operation.Operator.EQ, v3, v4);
		IntVariable v5 = new IntVariable("ee", 0, 99);
		Operation o4 = new Operation(Operation.Operator.EQ, v4, v5);
		Operation o34 = new Operation(Operation.Operator.AND, o3, o4);
		Operation o234 = new Operation(Operation.Operator.AND, o2, o34);
		check(solver, o1, o234, "(aa==bb)&&((bb==cc)&&((cc==dd)&&(dd==ee)))", "v0==v1", "v1==v2", "v2==v3", "v3==v4");
	}

	@Test
	public void test_05() {
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		Operation o1 = new Operation(Operation.Operator.EQ, v1, v2);
		IntVariable v3 = new IntVariable("cc", 0, 99);
		Operation o2 = new Operation(Operation.Operator.EQ, v2, v3);
		IntVariable v4 = new IntVariable("dd", 0, 99);
		Operation o3 = new Operation(Operation.Operator.EQ, v3, v4);
		IntVariable v5 = new IntVariable("ee", 0, 99);
		IntVariable v6 = new IntVariable("ff", 0, 99);
		Operation o4 = new Operation(Operation.Operator.EQ, v5, v6);
		Operation o34 = new Operation(Operation.Operator.AND, o3, o4);
		Operation o234 = new Operation(Operation.Operator.AND, o2, o34);
		check(solver, o1, o234, "(aa==bb)&&((bb==cc)&&((cc==dd)&&(ee==ff)))", "v0==v1", "v1==v2", "v2==v3", "v4==v5");
	}

	@Test
	public void test_06() {
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		IntVariable v3 = new IntVariable("cc", 0, 99);
		IntVariable v4 = new IntVariable("dd", 0, 99);
		IntVariable v5 = new IntVariable("ee", 0, 99);
		IntVariable v6 = new IntVariable("ff", 0, 99);
		IntVariable v7 = new IntVariable("gg", 0, 99);
		Operation o1 = new Operation(Operation.Operator.LT, v1, new Operation(Operation.Operator.ADD, v2, v3));
		Operation o2 = new Operation(Operation.Operator.LT, v2, new Operation(Operation.Operator.ADD, v4, v5));
		Operation o3 = new Operation(Operation.Operator.LT, v3, new Operation(Operation.Operator.ADD, v6, v7));
		Operation o23 = new Operation(Operation.Operator.AND, o2, o3);
		check(solver, o1, o23, "(aa<(bb+cc))&&((bb<(dd+ee))&&(cc<(ff+gg)))", "v0<v1+v2", "v1<v3+v4", "v2<v5+v6");
	}

	@Test
	public void test_07() {
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		IntVariable v3 = new IntVariable("cc", 0, 99);
		IntVariable v4 = new IntVariable("dd", 0, 99);
		IntVariable v5 = new IntVariable("ee", 0, 99);
		IntVariable v6 = new IntVariable("ff", 0, 99);
		IntVariable v7 = new IntVariable("gg", 0, 99);
		IntVariable v8 = new IntVariable("hh", 0, 99);
		Operation o1 = new Operation(Operation.Operator.LT, v1, new Operation(Operation.Operator.ADD, v2, v3));
		Operation o2 = new Operation(Operation.Operator.LT, v2, new Operation(Operation.Operator.ADD, v4, v5));
		Operation o3 = new Operation(Operation.Operator.LT, v6, new Operation(Operation.Operator.ADD, v7, v8));
		Operation o23 = new Operation(Operation.Operator.AND, o2, o3);
		check(solver, o1, o23, "(aa<(bb+cc))&&((bb<(dd+ee))&&(ff<(gg+hh)))", "v0<v1+v2", "v1<v3+v4", "v5<v6+v7");
	}

	@Test
	public void test_08() {
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		IntVariable v3 = new IntVariable("cc", 0, 99);
		Operation o1 = new Operation(Operation.Operator.ADD, v1, v2);
		Operation o2 = new Operation(Operation.Operator.ADD, v1, v3);
		Operation o3 = new Operation(Operation.Operator.LT, o1, o2);
		check(solver, o3, "(aa+bb)<(aa+cc)", "v0+v1<v0+v2");
	}

	@Test
	public void test_09() {
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		IntVariable v3 = new IntVariable("cc", 0, 99);
		Operation o1 = new Operation(Operation.Operator.ADD, v1, v2);
		Operation o2 = new Operation(Operation.Operator.SUB, v1, v3);
		Operation o3 = new Operation(Operation.Operator.LT, o1, o2);
		check(solver, o3, "(aa+bb)<(aa-cc)", "v0+v1<v0-v2");
	}

	@Test
	public void test_10() {
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		Operation o1 = new Operation(Operation.Operator.ADD, v1, v2);
		Operation o2 = new Operation(Operation.Operator.SUB, v2, v1);
		Operation o3 = new Operation(Operation.Operator.LT, o1, o2);
		check(solver, o3, "(aa+bb)<(bb-aa)", "v0+v1<v1-v0");
	}

	@Test
	public void test_11() {
		IntConstant c1 = new IntConstant(2);
		IntConstant c2 = new IntConstant(3);
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		Operation o1 = new Operation(Operation.Operator.ADD, c1, c2);
		Operation o2 = new Operation(Operation.Operator.MUL, o1, v1);
		Operation o3 = new Operation(Operation.Operator.LT, o2, v2);
		check(solver, o3, "((2+3)*aa)<bb", "2+3*v0<v1");
	}

	@Test
	public void test_12() {
		IntConstant c1 = new IntConstant(2);
		IntVariable v1 = new IntVariable("aa", 0, 99);
		IntVariable v2 = new IntVariable("bb", 0, 99);
		Operation o1 = new Operation(Operation.Operator.SUB, v1, v2);
		Operation o2 = new Operation(Operation.Operator.MUL, o1, c1);
		Operation o3 = new Operation(Operation.Operator.LT, o2, v1);
		check(solver, o3, "((aa-bb)*2)<aa", "v0-v1*2<v0");
	}

	@Test
	public void test_13() {
		IntConstant c1 = new IntConstant(2);
		Operation o1 = new Operation(Operation.Operator.LT, c1, c1);
		check(solver, o1, "2<2", "2<2");
	}

	@Test
	public void test_14() {
		IntConstant c1 = new IntConstant(2);
		IntVariable v1 = new IntVariable("aa", 0, 99);
		Operation o1 = new Operation(Operation.Operator.LT, c1, c1);
		Operation o2 = new Operation(Operation.Operator.LT, v1, c1);
		Operation o3 = new Operation(Operation.Operator.AND, o1, o2);
		check(solver, o3, "(2<2)&&(aa<2)", "2<2", "v0<2");
	}

	@Test
	public void test_15() {
		IntVariable x5 = new IntVariable("x5", 0, 99);
		Operation o2b = new Operation(Operation.Operator.NE, x5, x5);
		Operation o2a = new Operation(Operation.Operator.NOT, o2b);
		check(solver, o2a, "!(x5!=x5)", "!v0!=v0");
	}

}
