package za.ac.sun.cs.green.service.smtlib;

import static org.junit.Assert.*;

import java.util.Map;
import java.util.Properties;
import org.junit.BeforeClass;
import org.junit.Test;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.*;
import za.ac.sun.cs.green.util.Configuration;

public class ModelSMTLIBBitVectorServiceTest {

	private static final String DEFAULT_Z3_PATH = "/usr/bin/z3";
	public static Green solver;

    @BeforeClass
    public static void initialize() {
        solver = new Green();
        Properties props = new Properties();
        props.setProperty("green.services", "model");
        props.setProperty("green.service.model", "(z3)");
        //props.setProperty("green.service.model.smtlib", "za.ac.sun.cs.green.service.smtlib.ModelSMTLIBBitVectorService");
        props.setProperty("green.service.model.z3", "za.ac.sun.cs.green.service.z3.ModelZ3BitVectorService");
        props.setProperty("green.z3.path", DEFAULT_Z3_PATH);
        Configuration config = new Configuration(solver, props);
        config.configure();
    }
    
	@Test
	public void test01() {
		RealVariable v = new RealVariable("v", 0.0, 99.0);
		RealConstant c = new RealConstant(0.5);
		Operation o = new Operation(Operation.Operator.GE, v, c);
		Instance in = new Instance(solver, null, o);
		Map<IntVariable, IntConstant> model = (Map<IntVariable, IntConstant>) in.request("model");
		//ModelSMTLIBBitVectorService in2 = (ModelSMTLIBBitVectorService) in.request("smtlib");
	}

}
