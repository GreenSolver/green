package za.ac.sun.cs.green.service.barvinok;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;

import org.apfloat.Apint;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.util.Configuration;

public class CountBarvinokTest {

	public static Green solver = null;

	private static final String BARVINOK_PATH = "barvinoklattepath";
	private static final String RESOURCE_NAME = "build.properties";

	@BeforeClass
	public static void initialize() {
		solver = new Green();
		Properties properties = new Properties();
		properties.setProperty("green.services", "count");
		properties.setProperty("green.service.count", "barvinok");
		properties.setProperty("green.service.count.barvinok",
				"za.ac.sun.cs.green.service.barvinok.CountBarvinokService");

		String barvPath = new File("").getAbsolutePath() + "/lib/barvinok-0.39/barvlatte";
		ClassLoader loader = Thread.currentThread().getContextClassLoader();
		InputStream resourceStream;
		try {
			resourceStream = loader.getResourceAsStream(RESOURCE_NAME);
			if (resourceStream == null) {
				// If properties are correct, override with that specified path.
				resourceStream = new FileInputStream((new File("").getAbsolutePath()) + "/" + RESOURCE_NAME);

			}
			if (resourceStream != null) {
				properties.load(resourceStream);
				barvPath = properties.getProperty(BARVINOK_PATH);
				resourceStream.close();
			}
		} catch (IOException x) {
			// ignore
		}

		properties.setProperty("green.barvinok.path", barvPath);
		Configuration config = new Configuration(solver, properties);
		config.configure();
	}

	@AfterClass
	public static void report() {
		if (solver != null) {
			solver.report();
		}
	}

	private void check(Expression expression, Expression parentExpression, Apint expected) {
		Instance p = (parentExpression == null) ? null : new Instance(solver, null, parentExpression);
		Instance i = new Instance(solver, p, expression);
		Object result = i.request("count");
		assertNotNull(result);
		assertEquals(Apint.class, result.getClass());
		assertEquals(expected, result);
	}

	private void check(Expression expression, Apint expected) {
		check(expression, null, expected);
	}

	/**
	 * Problem: 1 * aa == 0 Count: 1
	 */
	@Test
	public void test01() {
		IntConstant a = new IntConstant(1);
		IntVariable v = new IntVariable("aa", 0, 99);
		Operation t = new Operation(Operation.Operator.MUL, a, v);
		IntConstant c = new IntConstant(0);
		Operation o = new Operation(Operation.Operator.EQ, t, c);
		check(o, new Apint(1));
	}

	/**
	 * Problem: 1 * aa > 0 1 * aa + -10 < 0 Count: 9
	 */
	@Test
	public void test02() {
		IntConstant zz = new IntConstant(0);
		IntConstant oo = new IntConstant(1);
		IntVariable vv = new IntVariable("aa", 0, 99);

		Operation at = new Operation(Operation.Operator.MUL, oo, vv);
		Operation ao = new Operation(Operation.Operator.GT, at, zz);

		Operation bt1 = new Operation(Operation.Operator.MUL, oo, vv);
		Operation bt2 = new Operation(Operation.Operator.ADD, bt1, new IntConstant(-10));
		Operation bo = new Operation(Operation.Operator.LT, bt2, zz);

		Operation o = new Operation(Operation.Operator.AND, ao, bo);
		check(o, new Apint(9));
	}

	/**
	 * Problem: 3 * aa + -6 > 0 1 * aa + -10 < 0 Count: 7
	 */
	@Test
	public void test03() {
		IntConstant zz = new IntConstant(0);
		IntConstant oo = new IntConstant(1);
		IntConstant tt = new IntConstant(3);
		IntVariable vv = new IntVariable("aa", 0, 99);

		Operation at1 = new Operation(Operation.Operator.MUL, tt, vv);
		Operation at2 = new Operation(Operation.Operator.ADD, at1, new IntConstant(-6));
		Operation ao = new Operation(Operation.Operator.GT, at2, zz);

		Operation bt1 = new Operation(Operation.Operator.MUL, oo, vv);
		Operation bt2 = new Operation(Operation.Operator.ADD, bt1, new IntConstant(-10));
		Operation bo = new Operation(Operation.Operator.LT, bt2, zz);

		Operation o = new Operation(Operation.Operator.AND, ao, bo);
		check(o, new Apint(7));
	}

	/**
	 * Problem: 1 * aa + -1 * bb < 0 1 * aa + 1 > 0 1 * aa + -10 < 0 1 * bb + 1 > 0
	 * 1 * bb + -10 < 0 Count: 45
	 */
	@Test
	public void test04() {
		IntConstant zero = new IntConstant(0);
		IntConstant one = new IntConstant(1);
		IntConstant minone = new IntConstant(-1);
		IntConstant minten = new IntConstant(-10);
		IntVariable aa = new IntVariable("aa", 0, 9);
		IntVariable bb = new IntVariable("bb", 0, 9);

		Operation plusaa = new Operation(Operation.Operator.MUL, one, aa);
		Operation plusbb = new Operation(Operation.Operator.MUL, one, bb);
		Operation minbb = new Operation(Operation.Operator.MUL, minone, bb);

		Operation oab1 = new Operation(Operation.Operator.ADD, plusaa, minbb);
		Operation oab = new Operation(Operation.Operator.LT, oab1, zero);
		Operation oa1 = new Operation(Operation.Operator.GT, new Operation(Operation.Operator.ADD, plusaa, one), zero);
		Operation oa2 = new Operation(Operation.Operator.LT, new Operation(Operation.Operator.ADD, plusaa, minten),
				zero);
		Operation ob1 = new Operation(Operation.Operator.GT, new Operation(Operation.Operator.ADD, plusbb, one), zero);
		Operation ob2 = new Operation(Operation.Operator.LT, new Operation(Operation.Operator.ADD, plusbb, minten),
				zero);

		Operation o3 = new Operation(Operation.Operator.AND, oab, oa1);
		Operation o2 = new Operation(Operation.Operator.AND, o3, oa2);
		Operation o1 = new Operation(Operation.Operator.AND, o2, ob1);
		Operation o = new Operation(Operation.Operator.AND, o1, ob2);

		check(o, new Apint(45));
	}

}
