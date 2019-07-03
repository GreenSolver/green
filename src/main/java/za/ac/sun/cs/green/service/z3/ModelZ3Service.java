package za.ac.sun.cs.green.service.z3;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;
import java.util.stream.Collectors;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.RealConstant;
import za.ac.sun.cs.green.expr.RealVariable;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.service.smtlib.ModelSMTLIBService;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Z3 command-line model service.
 */
public class ModelZ3Service extends ModelSMTLIBService {

	/**
	 * The command to invoke Z3.
	 */
	protected final String z3Command;

	/**
	 * Milliseconds spent by this service.
	 */
	protected long timeConsumption = 0;

	/**
	 * Milliseconds used to compute a SAT result (including time to extra model).
	 */
	protected long satTimeConsumption = 0;

	/**
	 * Milliseconds used to compute an UNSAT result.
	 */
	protected long unsatTimeConsumption = 0;

	/**
	 * Milliseconds used to extract the model (if any).
	 */
	protected long modelParseTimeConsumption = 0;

	/**
	 * Construct an instance of the Z3 command-line service.
	 * 
	 * @param solver     associated Green solver
	 * @param properties properties used to construct the service
	 */
	public ModelZ3Service(Green solver, Properties properties) {
		super(solver);
		String p = properties.getProperty("green.z3.path");
		String a = properties.getProperty("green.z3.args");
		z3Command = p + ' ' + a;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * za.ac.sun.cs.green.service.smtlib.ModelSMTLIBService#report(za.ac.sun.cs.
	 * green.util.Reporter)
	 */
	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("timeConsumption", timeConsumption);
		reporter.report("  satTimeConsumption", satTimeConsumption);
		reporter.report("  unsatTimeConsumption", unsatTimeConsumption);
		reporter.report("modelParseTimeConsumption", modelParseTimeConsumption);
		super.report(reporter);
	}

	@Override
	protected Model resolve(String smtQuery, Map<Variable, String> variables) {
		long startTime = System.currentTimeMillis();
		try {
			Process process = Runtime.getRuntime().exec(z3Command);
			OutputStream stdin = process.getOutputStream();
			InputStream stdout = process.getInputStream();
			BufferedReader outReader = new BufferedReader(new InputStreamReader(stdout));

			stdin.write((smtQuery + "\n").getBytes());
			stdin.flush();
			String output = outReader.readLine();

			if ((output != null) && output.equals("unsat")) {
				stdin.close();
				stdout.close();
				process.destroy();
				unsatTimeConsumption += System.currentTimeMillis() - startTime;
				timeConsumption += System.currentTimeMillis() - startTime;
				return new Model(false, null);
			} else if ((output == null) || !output.equals("sat")) {
				log.fatal("Z3 returned a null: {}", output);
				stdin.close();
				stdout.close();
				process.destroy();
				timeConsumption += System.currentTimeMillis() - startTime;
				return null;
			}

			stdin.write("(get-model)(exit)\n".getBytes());
			stdin.flush();
			stdin.close();
			output = outReader.lines().collect(Collectors.joining());
			stdout.close();
			process.destroy();

			long startTime0 = System.currentTimeMillis();
			Map<Variable, Constant> model = parseModel(output, variables);
			modelParseTimeConsumption += System.currentTimeMillis() - startTime0;
			satTimeConsumption += System.currentTimeMillis() - startTime;
			timeConsumption += System.currentTimeMillis() - startTime;
			return new Model(true, model);
		} catch (IOException x) {
			log.fatal(x.getMessage(), x);
		}
		return null;
	}

	/**
	 * Parse the output of Z3 and reconstruct a variable assignment.
	 * 
	 * @param output    Z3 output
	 * @param variables mapping of variables to variables names
	 * @return the variable value assignment
	 */
	private Map<Variable, Constant> parseModel(String output, Map<Variable, String> variables) {
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

		Map<Variable, Constant> model = new HashMap<>();
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

}
