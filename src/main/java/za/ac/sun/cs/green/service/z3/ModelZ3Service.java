package za.ac.sun.cs.green.service.z3;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.*;
import za.ac.sun.cs.green.service.smtlib.ModelSMTLIBService;
import za.ac.sun.cs.green.util.Reporter;

import java.io.*;
import java.util.*;
import java.util.stream.Collectors;

import org.apache.logging.log4j.Level;

public class ModelZ3Service extends ModelSMTLIBService {

	private final String DEFAULT_Z3_PATH;

	private final String DEFAULT_Z3_ARGS = "-smt2 -in";

	private final String z3Command;

	/**
	 * Execution Time of the service.
	 */
	private long timeConsumption = 0;
	private long satTimeConsumption = 0;
	private long unsatTimeConsumption = 0;

	public ModelZ3Service(Green solver, Properties properties) {
		super(solver);
		String DRIVE = new File("").getAbsolutePath() + "/";
		String sub = "lib/z3/build/z3";
		String z3Path = DRIVE+sub;
		InputStream is = SATZ3Service.class.getClassLoader()
				.getResourceAsStream("green/build.properties");
		if (is != null) {
			Properties p = new Properties();
			try {
				p.load(is);
				z3Path = p.getProperty("z3path");
			} catch (IOException e) {
				// do nothing
			}
		}

		DEFAULT_Z3_PATH = z3Path;
		String p = properties.getProperty("green.z3.path", DEFAULT_Z3_PATH);
		String a = properties.getProperty("green.z3.args", DEFAULT_Z3_ARGS);
		z3Command = p + ' ' + a;
	}

	@Override
	protected Map<Variable, Object> solve0(String smtQuery, Map<Variable, String> variables) {
		long startTime = System.currentTimeMillis();
		try {
			Process process = Runtime.getRuntime().exec(z3Command);
			OutputStream stdin = process.getOutputStream();
			InputStream stdout = process.getInputStream();
			BufferedReader outReader = new BufferedReader(new InputStreamReader(stdout));

			stdin.write((smtQuery + "\n").getBytes());
			stdin.flush();
			String output = outReader.readLine();

			if (output.equals("unsat")) {
				long a = System.currentTimeMillis() - startTime;
				timeConsumption += a;
				unsatTimeConsumption += a;
				stdin.close();
				stdout.close();
				process.destroy();
				return null;
			} else if (!output.equals("sat")) {
				log.fatal("Z3 returned a null: " + output);
				stdin.close();
				stdout.close();
				process.destroy();
				return null;
			}

			stdin.write("(get-model)(exit)\n".getBytes());
			stdin.flush();
			stdin.close();
            output = outReader.lines().collect(Collectors.joining());
			stdout.close();
			process.destroy();

			long a = System.currentTimeMillis() - startTime;
			timeConsumption += a;
			Map<Variable,Object> tmp = retrieveModel(output, variables);
			satTimeConsumption += a;
			return tmp;
		} catch (IOException x) {
			log.log(Level.FATAL, x.getMessage(), x);
		}
        return null;
	}

    private Map<Variable, Object> retrieveModel(String output, Map<Variable, String> variables) {
		output = output.replaceAll("^\\s*\\(model\\s+(.*)\\s*\\)\\s*$", "$1@");
        output = output.replaceAll("\\)\\s*\\(define-fun", ")@(define-fun");
        output = output.replaceAll("\\(define-fun\\s+([\\w-]+)\\s*\\(\\)\\s*[\\w]+\\s+([^@]+)\\s*\\)@", "$1 == $2 ;; ");

		final Map<String, String> assignment = new HashMap<>();
		for (String asgn : output.split(";;")) {
		    if (asgn.contains("==")) {
                String[] pair = asgn.split("==");
                assignment.put(pair[0].trim(), pair[1].trim());
            }
        }

		HashMap<Variable, Object> model = new HashMap<>();
		for (Map.Entry<Variable, String> entry : variables.entrySet()) {
		    Variable var = entry.getKey();
		    String name = entry.getValue();
		    if (assignment.containsKey(name)) {
                Constant value = null;
                if (var instanceof IntVariable) {
                	String val = assignment.get(name);
					val = val.replaceAll("\\(\\s*-\\s*(.+)\\)", "-$1");
					value = new IntConstant(Integer.parseInt(val));
				} else if (var instanceof RealVariable) {
                    value = new RealConstant(Double.parseDouble(assignment.get(name)));
                }
		        if (value != null) {
                    model.put(var, value);
                }
            }
        }
		return model;
	}

	@Override
	public void report(Reporter reporter) {
		reporter.report(getClass().getSimpleName(), "timeConsumption = " + timeConsumption);
		reporter.report(getClass().getSimpleName(), "satTimeConsumption = " + satTimeConsumption);
		reporter.report(getClass().getSimpleName(), "unsatTimeConsumption = " + unsatTimeConsumption);
	}

}
