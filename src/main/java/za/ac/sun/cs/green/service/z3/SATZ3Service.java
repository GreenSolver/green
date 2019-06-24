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

public class SATZ3Service extends SATSMTLIBService {

	private final String z3Command;

	private long timeConsumption = 0;
	private long satTimeConsumption = 0;
	private long unsatTimeConsumption = 0;

	public SATZ3Service(Green solver, Properties properties) {
		super(solver);
		String p = properties.getProperty("green.z3.path");
		String a = properties.getProperty("green.z3.args");
		z3Command = p + ' ' + a;
	}

	@Override
	protected Boolean solve0(String smtQuery) {
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
		long a = System.currentTimeMillis() - startTime;
		timeConsumption += a;
		if (output.equals("sat")) {
			satTimeConsumption += a;
			return true;
		} else if (output.equals("unsat")) {
			unsatTimeConsumption += a;
			return false;
		} else {
			log.fatal("Z3 returned a null {}", output);
			return null;
		}
	}

	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("cacheHitCount", cacheHitCount);
		reporter.report("cacheMissCount", cacheMissCount);
		reporter.report("satCacheHitCount", satHitCount);
		reporter.report("unsatCacheHitCount", unsatHitCount);
		reporter.report("satCacheMissCount", satMissCount);
		reporter.report("unsatCacheMissCount", unsatMissCount);
		reporter.report("satQueries", satCount);
		reporter.report("unsatQueries", unsatCount);
		reporter.report("timeConsumption", timeConsumption);
		reporter.report("satTimeConsumption", satTimeConsumption);
		reporter.report("unsatTimeConsumption", unsatTimeConsumption);
		reporter.report("storageTimeConsumption", storageTimeConsumption);
		reporter.report("translationTimeConsumption", translationTimeConsumption);
		reporter.report("conjunctCount", conjunctCount);
		reporter.report("varCount", varCount);
	}
}
