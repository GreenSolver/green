package za.ac.sun.cs.green.service.simplify;

import static org.junit.Assert.*;

import java.util.Arrays;
import java.util.Properties;
import java.util.SortedSet;
import java.util.TreeSet;

import org.junit.BeforeClass;
import org.junit.Test;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.util.Configuration;

public class SimplificationConstantPropogationTest {

	public static Green solver;

	@BeforeClass
		public static void initialize() {
			solver = new Green();
			Properties props = new Properties();
			props.setProperty("green.services", "sat");
			props.setProperty("green.service.sat", "(simplify sink)");
			//props.setProperty("green.service.sat", "(canonize sink)");
			props.setProperty("green.service.sat.simplify",
					"za.ac.sun.cs.green.service.simplify.ConstantPropogation");
			//props.setProperty("green.service.sat.canonize",
			//		"za.ac.sun.cs.green.service.canonizer.SATCanonizerService");
			
			props.setProperty("green.service.sat.sink",
					"za.ac.sun.cs.green.service.sink.SinkService");
			Configuration config = new Configuration(solver, props);
			config.configure();
		}

	private void finalCheck(String observed, String expected) {
		assertEquals(expected, observed);
	}

	private void check(Expression expression, String expected) {
		Instance i = new Instance(solver, null, null, expression);
		Expression e = i.getExpression();
		assertTrue(e.equals(expression));
		assertEquals(expression.toString(), e.toString());
		Object result = i.request("sat");
		assertNotNull(result);
		assertEquals(Instance.class, result.getClass());
		Instance j = (Instance) result;
		finalCheck(j.getExpression().toString(), expected);
	}

	@Test
	public void test00() {
		IntVariable x = new IntVariable("x", 0, 99);
		IntVariable y = new IntVariable("y", 0, 99);
		IntVariable z = new IntVariable("z", 0, 99);
		IntConstant c = new IntConstant(1);
		IntConstant c10 = new IntConstant(10);
		IntConstant c3 = new IntConstant(3);
		Operation o1 = new Operation(Operation.Operator.EQ, x, c); // o1 : x = 1
		Operation o2 = new Operation(Operation.Operator.ADD, x, y); // o2 : (x + y)
		Operation o3 = new Operation(Operation.Operator.EQ, o2, c10); // o3 : x+y = 10
		Operation o4 = new Operation(Operation.Operator.AND, o1, o3); // o4 : x = 1 && (x+y) = 10 
		check(o4, "(x==1)&&(y==9)");
	}
	
	@Test
	public void test01() {
		IntVariable x = new IntVariable("x", 0, 99);
		IntVariable y = new IntVariable("y", 0, 99);
		IntConstant c = new IntConstant(1);
		IntConstant c2 = new IntConstant(10);
		IntConstant c3 = new IntConstant(2);
		Operation o1 = new Operation(Operation.Operator.EQ, x, c); // o1 : (x = 1)
		Operation o2 = new Operation(Operation.Operator.ADD, x, y); // o2 : x + y
		Operation o3 = new Operation(Operation.Operator.LT, o2, c2); // o3 : (x+y) < 10
		Operation oi = new Operation(Operation.Operator.SUB, y, c); // oi : y-1
		Operation o4 = new Operation(Operation.Operator.EQ, oi, c3); // o4 : y-1 = 2
		Operation o5 = new Operation(Operation.Operator.AND, o1, o3); // o5 : (x = 1) && (x+y < 10)
		Operation o = new Operation(Operation.Operator.AND, o5, o4); // o = (x = 1) && (x+y < 10) && (y-1 = 2)
		// (x = 1) && (x+y < 10) && (y-1 = 2)
		check(o, "(x==1)&&(y==3)");
	}

	@Test
		public void test02() {
			IntConstant c1 = new IntConstant(4);
			IntConstant c2 = new IntConstant(10);
			Operation o = new Operation(Operation.Operator.LT, c1, c2);
			check(o, "0==0");
		}

	@Test
		public void test03() {
			IntConstant c1 = new IntConstant(4);
			IntConstant c2 = new IntConstant(10);
			Operation o = new Operation(Operation.Operator.GT, c1, c2);
			check(o, "0==1");
		}

	@Test
		public void test04() {
			IntConstant c1 = new IntConstant(4);
			IntConstant c2 = new IntConstant(10);
			Operation o1 = new Operation(Operation.Operator.LT, c1, c2);
			Operation o2 = new Operation(Operation.Operator.GT, c1, c2);
			Operation o = new Operation(Operation.Operator.AND, o1, o2);
			check(o, "0==1");
		}




	@Test
		public void test05() {
			IntVariable x = new IntVariable("x", 0, 99);
			IntVariable y = new IntVariable("y", 0, 99);		
			IntConstant c = new IntConstant(1);
			IntConstant c2 = new IntConstant(10);
			IntConstant c3 = new IntConstant(2);
			Operation o1 = new Operation(Operation.Operator.EQ, c, x);
			Operation o2 = new Operation(Operation.Operator.ADD, x, y);
			Operation o3 = new Operation(Operation.Operator.LT, o2, c2);
			Operation oi = new Operation(Operation.Operator.SUB, y, c);		
			Operation o4 = new Operation(Operation.Operator.EQ, c3, oi);
			Operation o5 = new Operation(Operation.Operator.AND, o1, o3);
			Operation o = new Operation(Operation.Operator.AND, o5, o4);
			check(o, "(1==x)&&(3==y)");
		}

	@Test
		public void test06() {
			IntVariable x = new IntVariable("x", 0, 99);
			IntVariable y = new IntVariable("y", 0, 99);
			IntVariable z = new IntVariable("z", 0 , 99);
			IntConstant c = new IntConstant(1);
			Operation o1 = new Operation(Operation.Operator.EQ, x, y);		
			Operation o2 = new Operation(Operation.Operator.EQ, y, z);
			Operation o3 = new Operation(Operation.Operator.EQ, z, c);
			Operation o = new Operation(Operation.Operator.AND, o1, o2);
			o = new Operation(Operation.Operator.AND, o, o3);
			check(o, "(x==1)&&((y==1)&&(z==1))");
		}

	@Test
		public void test07() {
			IntVariable x = new IntVariable("x", 0, 99);
			IntVariable y = new IntVariable("y", 0, 99);
			IntVariable z = new IntVariable("z", 0 , 99);
			IntConstant c = new IntConstant(2);
			IntConstant c1 = new IntConstant(4);
			Operation o1 = new Operation(Operation.Operator.MUL, x, y);		
			Operation o2 = new Operation(Operation.Operator.EQ, z, o1); // z = x * y
			Operation o3 = new Operation(Operation.Operator.EQ, x, c); // x = 2
			Operation o4 = new Operation(Operation.Operator.ADD, y, x); 
			Operation o5 = new Operation(Operation.Operator.EQ, o4, c1); // x+y = 4

			Operation o = new Operation(Operation.Operator.AND, o2, o3); // z = x * y && x = 2
			o = new Operation(Operation.Operator.AND, o, o5); // z = x * y && x = 2 && x+y = 4
			check(o, "(z==4)&&((x==2)&&(y==2))");
		}

	@Test
		public void test08() {
			IntVariable x = new IntVariable("x", 0, 99);
			IntConstant c = new IntConstant(2);
			IntConstant c1 = new IntConstant(4);
			Operation o1 = new Operation(Operation.Operator.EQ, x, c);		
			Operation o2 = new Operation(Operation.Operator.EQ, x, c1);
			Operation o = new Operation(Operation.Operator.AND, o1, o2);
			
			check(o, "0==1");
		}





}
