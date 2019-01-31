package za.ac.sun.cs.green.service.z3;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.Properties;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.service.smtlib.SATSMTLIBService;

public class SATZ3Service extends SATSMTLIBService {

	private final String DEFAULT_Z3_PATH;
	private final String DEFAULT_Z3_ARGS = "-smt2 -in";
	
	private final String z3Command;
	private final String resourceName = "build.properties";
	
	public SATZ3Service(Green solver, Properties properties) {
		super(solver);
		String z3Path = new File("").getAbsolutePath() + "/lib/z3/build/z3";
		ClassLoader loader = Thread.currentThread().getContextClassLoader();
		InputStream resourceStream;
		try {
		    resourceStream = loader.getResourceAsStream(resourceName);
		    if (resourceStream == null) {
			// If properties are correct, override with that specified path.
			resourceStream = new FileInputStream((new File("").getAbsolutePath()) + "/" + resourceName);

		    }
		    if (resourceStream != null) {
			properties.load(resourceStream);
			z3Path = properties.getProperty("z3path");

			resourceStream.close();
		    }
		} catch (IOException x) {
		    // ignore
		}

		DEFAULT_Z3_PATH = z3Path;
		
		String p = properties.getProperty("green.z3.path", DEFAULT_Z3_PATH);
		String a = properties.getProperty("green.z3.args", DEFAULT_Z3_ARGS);
		z3Command = p + ' ' + a;
	}

	@Override
	protected Boolean solve0(String smtQuery) {
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
		if (output.equals("sat")) {
			return true;
		} else if (output.equals("unsat")) {
			return false;
		} else {
			log.fatal("Z3 returned a null {}", output) ;
			return null;
		}
	}

}
