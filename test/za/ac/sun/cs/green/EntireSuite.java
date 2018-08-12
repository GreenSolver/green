package za.ac.sun.cs.green;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.HashMap;
import java.util.Properties;

import org.apache.commons.exec.CommandLine;
import org.apache.commons.exec.DefaultExecutor;
import org.apache.commons.exec.PumpStreamHandler;
import org.junit.runner.RunWith;
import org.junit.runners.Suite;

import com.microsoft.z3.Context;

import cvc3.ValidityChecker;
import za.ac.sun.cs.green.parser.smtlib2.SMTLIB2Parser0Test;
import za.ac.sun.cs.green.parser.smtlib2.SMTLIB2Scanner0Test;
import za.ac.sun.cs.green.service.bounder.BounderTest;
import za.ac.sun.cs.green.service.canonizer.SATCanonizerTest;
import za.ac.sun.cs.green.service.choco.SATChocoTest;
import za.ac.sun.cs.green.service.cvc3.SATCVC3Test;
import za.ac.sun.cs.green.service.factorizer.SATFactorizerTest;
import za.ac.sun.cs.green.service.latte.CountLattETest;
import za.ac.sun.cs.green.service.latte.CountLattEWithBounderTest;
import za.ac.sun.cs.green.service.simplify.OnlyConstantPropogationTest;
import za.ac.sun.cs.green.service.simplify.SimplificationConstantPropogationTest;
import za.ac.sun.cs.green.service.slicer.ParallelSATSlicerTest;
import za.ac.sun.cs.green.service.slicer.SATSlicerTest;
import za.ac.sun.cs.green.service.z3.SATZ3JavaTest;
import za.ac.sun.cs.green.service.z3.SATZ3Test;
import za.ac.sun.cs.green.util.ParallelSATTest;
import za.ac.sun.cs.green.util.SetServiceTest;
import za.ac.sun.cs.green.util.SetTaskManagerTest;

@RunWith(Suite.class)
@Suite.SuiteClasses({
    SimplificationConstantPropogationTest.class
})

public class EntireSuite {

	public static final String LATTE_PATH;

	public static final String BARVINOK_PATH;

	public static final String Z3_PATH;

	public static final boolean HAS_CVC3 = false;

	public static final boolean HAS_LATTE = false;

	public static final boolean HAS_Z3;

	public static final boolean HAS_Z3JAVA = false;

	static {
		String latte = null, z3 = null, barvinok = null;
		InputStream is = EntireSuite.class.getClassLoader()
				.getResourceAsStream("build.properties");
		if (is != null) {
			Properties p = new Properties();
			try {
				p.load(is);
				latte = p.getProperty("lattepath");
				barvinok = p.getProperty("barvinokpath");
				z3 = p.getProperty("z3path");
			} catch (IOException e) {
				// do nothing
			}
		}
		LATTE_PATH = latte;
		BARVINOK_PATH = barvinok;
		Z3_PATH = z3;
		HAS_Z3 = checkZ3Presence();
		if (!HAS_Z3) {
		  System.out.println("Z3 Not Available, no tests for it will be executed");	
		}
		
	}

	private static boolean checkCVC3Presence() {
		try {
			ValidityChecker.create();
		} catch (SecurityException x) {
			return false;
		} catch (UnsatisfiedLinkError x) {
			System.out.println("");
			x.printStackTrace();
			return false;
		}
		return true;
	}

	private static boolean checkLattEPresence() {
		if (LATTE_PATH == null) {
			return false;
		}
		final String DIRNAME = System.getProperty("java.io.tmpdir");
		String result = "";
		try {
			ByteArrayOutputStream outputStream = new ByteArrayOutputStream();
			DefaultExecutor executor = new DefaultExecutor();
			executor.setStreamHandler(new PumpStreamHandler(outputStream));
			executor.setWorkingDirectory(new File(DIRNAME));
			executor.setExitValues(null);
			executor.execute(CommandLine.parse(LATTE_PATH));
			result = outputStream.toString();
		} catch (IOException x) {
			x.printStackTrace();
			return false;
		}
		return result.trim().startsWith("This is LattE integrale");
	}

	private static boolean checkZ3Presence() {
		final String DIRNAME = System.getProperty("java.io.tmpdir");
		String result = "";
		try {
			ByteArrayOutputStream outputStream = new ByteArrayOutputStream();
			DefaultExecutor executor = new DefaultExecutor();
			executor.setStreamHandler(new PumpStreamHandler(outputStream));
			executor.setWorkingDirectory(new File(DIRNAME));
			executor.setExitValues(null);
			executor.execute(CommandLine.parse(Z3_PATH + " -h"));
			result = outputStream.toString();
		} catch (IOException e) {
			return false;
		}
		return result.startsWith("Z3 [version ");
	}

	private static boolean checkZ3JavaPresence() {
		HashMap<String, String> cfg = new HashMap<String, String>();
		cfg.put("model", "false");
		try {
			new Context(cfg);
		} catch (Exception x) {
			return false;
		} catch (UnsatisfiedLinkError x) {
			x.printStackTrace();
			return false;
		}
		return true;
	}

}
