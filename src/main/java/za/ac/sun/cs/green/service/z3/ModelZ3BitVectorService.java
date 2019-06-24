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

import org.apache.logging.log4j.Level;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.RealConstant;
import za.ac.sun.cs.green.expr.RealVariable;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.service.smtlib.ModelSMTLIBBitVectorService;
import za.ac.sun.cs.green.util.Reporter;

public class ModelZ3BitVectorService extends ModelSMTLIBBitVectorService {

	private final String z3Command;

	/**
	 * Execution Time of the service.
	 */
	private long timeConsumption = 0;
	private long satTimeConsumption = 0;
	private long unsatTimeConsumption = 0;

	public ModelZ3BitVectorService(Green solver, Properties properties) {
		super(solver);
		String p = properties.getProperty("green.z3.path");
		String a = properties.getProperty("green.z3.args");
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
				return null;
			} else if (!output.equals("sat")) {
				log.fatal("Z3 returned a null: " + output);
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
			System.out.println(output);
			Map<Variable, Object> tmp = retrieveModel(output, variables);
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
		reporter.setContext(getClass().getSimpleName());
		reporter.report("timeConsumption", timeConsumption);
		reporter.report("satTimeConsumption", satTimeConsumption);
		reporter.report("unsatTimeConsumption", unsatTimeConsumption);
	}

}
