package za.ac.sun.cs.green.service.smtlib;

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.util.Map;
import java.util.Properties;

import org.junit.BeforeClass;
import org.junit.Test;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Operation.Operator;
import za.ac.sun.cs.green.expr.RealConstant;
import za.ac.sun.cs.green.expr.RealVariable;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.util.Configuration;

public class ModelSMTLIBFloatServiceTest {

	public static Green solver;

	@BeforeClass
	public static void initialize() {
		solver = new Green();
		Properties props = new Properties();
		props.setProperty("green.services", "model");
		props.setProperty("green.service.model", "(z3)");
		props.setProperty("green.service.model.z3", "za.ac.sun.cs.green.service.z3.ModelZ3FloatService");
		Configuration config = new Configuration(solver, props);
		config.configure();
	}

	@Test
	public void test01() {
		RealVariable v = new RealVariable("v", -99.0, 99.0, 32);
		RealConstant c = new RealConstant(-0.5);
		Operation o = new Operation(Operation.Operator.LE, v, c);

		Instance in = new Instance(solver, null, o);
		@SuppressWarnings("unchecked")
		Map<Variable, Object> model = (Map<Variable, Object>) in.request("model");

		Object output = model.get(v);
		assert (output instanceof RealConstant);

		double out = Double.parseDouble(output.toString());
		assertTrue(out <= -0.5);
		assertTrue(out >= -99.0);
	}

	@Test
	public void test02() {
		IntVariable v = new IntVariable("v", -99, 99);
		IntConstant c = new IntConstant(20);
		Operation o = new Operation(Operation.Operator.LE, v, c);

		Instance in = new Instance(solver, null, o);
		@SuppressWarnings("unchecked")
		Map<Variable, Object> model = (Map<Variable, Object>) in.request("model");
		assertNotNull(model);

		Object output = model.get(v);
		assertTrue(output instanceof IntConstant);

		int out = Integer.parseInt(output.toString());
		assertTrue(out <= 20 && out >= -99);
	}

	@Test
	public void test03() {
		IntVariable v1 = new IntVariable("v1", 0, 50);
		IntConstant c1 = new IntConstant(2);
		RealVariable v2 = new RealVariable("v2", 0.0, 50.0, 32);
		RealConstant c2 = new RealConstant(25.5);

		Operation t1 = new Operation(Operator.GT, v2, c2);
		Operation t2 = new Operation(Operator.LT, v1, c1);
		Operation t3 = new Operation(Operator.NE, v1, v2);
		Operation o = new Operation(Operator.AND, new Operation(Operator.AND, t1, t2), t3);

		Instance in = new Instance(solver, null, o);
		@SuppressWarnings("unchecked")
		Map<Variable, Object> model = (Map<Variable, Object>) in.request("model");
		assertNotNull(model);

		Object v1Val = model.get(v1);
		Object v2Val = model.get(v2);
		assertTrue(v1Val instanceof IntConstant);
		assertTrue(v2Val instanceof RealConstant);

		int val1 = Integer.parseInt(v1Val.toString());
		double val2 = Double.parseDouble(v2Val.toString());
		assertTrue(val1 >= 0 && val1 < 2);
		assertTrue(val2 > 25.5 && val2 <= 50.0);
		assertTrue(val2 != val1);
	}

	@Test
	public void test04() {
		IntConstant c1 = new IntConstant(1);
		RealConstant c2 = new RealConstant(1.5);
		IntVariable v1 = new IntVariable("v1", 0, 2);

		Operation t1 = new Operation(Operator.GT, v1, c1);
		Operation t2 = new Operation(Operator.LT, v1, c2);
		Operation o = new Operation(Operator.AND, t1, t2);

		Instance in = new Instance(solver, null, o);
		@SuppressWarnings("unchecked")
		Map<Variable, Object> model = (Map<Variable, Object>) in.request("model");
		assertNull(model);
	}

}
