package za.ac.sun.cs.green.service.z3;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.Properties;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.service.smtlib.SATSMTLIBService;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Z3 command-line SAT service.
 */
public class SATZ3Service extends SATSMTLIBService {

	/**
	 * The command to invoke Z3.
	 */
	protected final String z3Command;

	/**
	 * Milliseconds spent by this service.
	 */
	protected long timeConsumption = 0;

	/**
	 * Milliseconds used to compute a SAT result.
	 */
	protected long satTimeConsumption = 0;

	/**
	 * Milliseconds used to compute an UNSAT result.
	 */
	protected long unsatTimeConsumption = 0;

	/**
	 * Construct an instance of the Z3 command-line service.
	 * 
	 * @param solver     associated Green solver
	 * @param properties properties used to construct the service
	 */
	public SATZ3Service(Green solver, Properties properties) {
		super(solver);
		String p = properties.getProperty("green.z3.path");
		String a = properties.getProperty("green.z3.args");
		z3Command = p + ' ' + a;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * za.ac.sun.cs.green.service.smtlib.SATSMTLIBService#report(za.ac.sun.cs.green.
	 * util.Reporter)
	 */
	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("timeConsumption", timeConsumption);
		reporter.report("  satTimeConsumption", satTimeConsumption);
		reporter.report("  unsatTimeConsumption", unsatTimeConsumption);
		super.report(reporter);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * za.ac.sun.cs.green.service.smtlib.SATSMTLIBService#resolve(java.lang.String)
	 */
	@Override
	protected Boolean resolve(String smtQuery) {
		long startTime = System.currentTimeMillis();
		String output = "";
		try {
			Process process = Runtime.getRuntime().exec(z3Command);
			OutputStream stdin = process.getOutputStream();
			InputStream stdout = process.getInputStream();
			BufferedReader outReader = new BufferedReader(new InputStreamReader(stdout));
			stdin.write((smtQuery + "(exit)\n").getBytes());
			stdin.flush();
			stdin.close();
			output = outReader.readLine();
			stdout.close();
			process.destroy();
		} catch (IOException x) {
			log.fatal(x.getMessage(), x);
		}
		timeConsumption += System.currentTimeMillis() - startTime;
		if ((output != null) && output.equals("sat")) {
			satTimeConsumption += System.currentTimeMillis() - startTime;
			return true;
		} else if ((output != null) && output.equals("unsat")) {
			unsatTimeConsumption += System.currentTimeMillis() - startTime;
			return false;
		} else {
			log.fatal("Z3 returned a null: {}", output);
			return null;
		}
	}

}
