package za.ac.sun.cs.green.service.z3;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.stream.Collectors;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.RealConstant;
import za.ac.sun.cs.green.expr.RealVariable;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.service.smtlib.ModelCoreSMTLIBService;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Z3 command-line model service.
 */
public class ModelCoreZ3Service extends ModelCoreSMTLIBService {

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
	 * Milliseconds used to extract the core (if any).
	 */
	protected long coreParseTimeConsumption = 0;

	/**
	 * Construct an instance of the Z3 command-line service.
	 * 
	 * @param solver     associated Green solver
	 * @param properties properties used to construct the service
	 */
	public ModelCoreZ3Service(Green solver, Properties properties) {
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
		reporter.report("coreParseTimeConsumption", coreParseTimeConsumption);
		super.report(reporter);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * za.ac.sun.cs.green.service.smtlib.ModelCoreSMTLIBService#resolve(java.lang.
	 * String, java.util.Map, java.util.Map)
	 */
	@Override
	protected ModelCore resolve(String smtQuery, Map<Variable, String> variables,
			Map<String, Expression> coreClauseMapping) {
		log.trace("smtQuery: {}", smtQuery);
		long startTime = System.currentTimeMillis();
		try {
			Process process = Runtime.getRuntime().exec(z3Command);
			OutputStream stdin = process.getOutputStream();
			InputStream stdout = process.getInputStream();
			BufferedReader outReader = new BufferedReader(new InputStreamReader(stdout));
			stdin.write((smtQuery + "\n").getBytes());
			stdin.flush();
			String output = outReader.readLine();

			boolean isSat = false;
			if (output != null) {
				switch (output) {
				case "sat":
					smtQuery = "(get-model)";
					isSat = true;
					break;
				case "unsat":
					smtQuery = "(get-unsat-core)";
					break;
				default:
					log.fatal("Z3 returned a null: " + output);
					return null;
				}
			} else {
				log.fatal("Z3 returned a null: " + output);
				return null;
			}

			stdin.write((smtQuery + "(exit)\n").getBytes());
			stdin.flush();
			stdin.close();
			output = outReader.lines().collect(Collectors.joining());
			stdout.close();
			process.destroy();

			Map<Variable, Constant> model = null;
			Set<Expression> core = null;
			if (isSat) {
				long startTime0 = System.currentTimeMillis();
				model = parseModel(output, variables);
				modelParseTimeConsumption += System.currentTimeMillis() - startTime0;
				satTimeConsumption += System.currentTimeMillis() - startTime;
			} else {
				long startTime0 = System.currentTimeMillis();
				core = parseCore(output, coreClauseMapping);
				coreParseTimeConsumption += System.currentTimeMillis() - startTime0;
				unsatTimeConsumption += (System.currentTimeMillis() - startTime);
			}
			timeConsumption += (System.currentTimeMillis() - startTime);
			return new ModelCore(isSat, model, core);
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
					String val = assignment.get(name);
					if (val.contains("/")) {
						val = val.replaceAll("\\(\\s*-\\s*\\(\\s*/\\s*(.+)\\s*\\)\\s*\\)", "(/ -$1)");
						val = val.replaceAll("\\(\\s*/\\s*(.+)\\s*(.+)\\s*\\)", "$1/$2");
						String[] rat = val.split("/");
						double num = Double.parseDouble(rat[0]);
						double den = Double.parseDouble(rat[1]);
						value = new RealConstant(num / den);
					} else {
						val = val.replaceAll("\\(\\s*-\\s*(.+)\\)", "-$1");
						value = new RealConstant(Double.parseDouble(val));
					}
				}
				if (value != null) {
					model.put(var, value);
				}
			}
		}
		return model;
	}

	/**
	 * Parse the output of Z3 and reconstruct an unsatisfiable core.
	 * 
	 * @param output            Z3 output
	 * @param coreClauseMapping mapping from clause names to Green expressions
	 * @return the set of expressions that form an unsatisfiable core
	 */
	private Set<Expression> parseCore(String output, Map<String, Expression> coreClauseMapping) {
		String[] clauseNames = output.replaceAll("^\\s*\\(\\s*([^\\s].*[^\\s]*)\\s*\\)\\s*$", "$1").split("\\s+");
		Set<Expression> clauses = new HashSet<>();
		for (String namedClause : clauseNames) {
			Expression realClause = coreClauseMapping.get(namedClause);
			if (realClause != null) {
				clauses.add(realClause);
			}
		}
		return clauses;
	}

}
