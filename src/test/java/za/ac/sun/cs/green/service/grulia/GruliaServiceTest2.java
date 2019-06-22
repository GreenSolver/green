package za.ac.sun.cs.green.service.grulia;

import static org.junit.Assert.assertEquals;

import java.util.Properties;

import org.junit.After;
import org.junit.BeforeClass;
import org.junit.Test;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.parser.sexpr.LIAParser;
import za.ac.sun.cs.green.util.Configuration;

/**
 * Simple Grulia test
 * 
 * @date: 2018/08/23
 * @author: JH Taljaard (USnr 18509193)
 * @contributor: Willem Visser (2018, 2019) (supervisor)
 * @contributor: Jaco Geldenhuys (2017) (supervisor)
 */
public class GruliaServiceTest2 {
	public static Green solver;

	@BeforeClass
	public static void initialize() {
		solver = new Green();
		Properties props = new Properties();
		props.setProperty("green.services", "sat");
		props.setProperty("green.service.sat", "(factor (renamer grulia))");
		props.setProperty("green.service.sat.factor", "za.ac.sun.cs.green.service.factorizer.SATFactorizerService");
		props.setProperty("green.service.sat.renamer", "za.ac.sun.cs.green.service.renamer.RenamerService");
		props.setProperty("green.service.sat.grulia", "za.ac.sun.cs.green.service.grulia.GruliaService");

		Configuration config = new Configuration(solver, props);
		config.configure();
	}

//	@Before
//	public void reset() {
//		GruliaService.reset();
//	}

	@After
	public void report2() {
		solver.report();
	}

	private boolean check(Expression expression) {
		Instance i = new Instance(solver, null, expression);
		Object result = i.request("sat");
		return result.toString().equals("true");
	}

	private void check(String input, boolean expected) {
		try {
			LIAParser parser = new LIAParser();
			Operation o = parser.parse(input);
			boolean ans = check(o);
			assertEquals(expected, ans);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	@Test
	public void modelTest() {
		StringBuilder query1 = new StringBuilder();
		query1 = query1.append("4\n").append("1 lt * 2 c -1 v 0 c 0\n").append("1 lt * 2 c -1 v 0 c 1\n")
				.append("1 lt * 2 c -1 v 1 c 0\n").append("1 lt * 2 c -1 v 2 c 1\n");

		StringBuilder query2 = new StringBuilder();
		query2 = query2.append("4\n").append("1 lt * 2 c -1 v 0 c 0\n").append("1 lt * 2 c -1 v 1 c 0\n")
				.append("1 lt * 2 c -1 v 0 c 1\n").append("1 lt * 2 c -1 v 2 c 1\n");

		check(query1.toString(), true);
		check(query2.toString(), true);
	}

	@Test
	public void unsatcoreTest() {
		StringBuilder query1 = new StringBuilder();
		query1 = query1.append("3\n").append("1 lt * 2 c -1 v 1 c 0\n").append("1 lt * 2 c -1 v 1 c 1\n")
				.append("1 lt * 2 c 1 v 1 c 1\n");
		check(query1.toString(), false);

		StringBuilder query2 = new StringBuilder();
		query2 = query2.append("3\n").append("1 lt * 2 c -1 v 1 c 1\n").append("1 lt * 2 c -1 v 1 c 0\n")
				.append("1 lt * 2 c 1 v 1 c 1\n");
		check(query2.toString(), false);
	}
}
