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

import org.apache.logging.log4j.Level;

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

public class ModelCoreZ3Service extends ModelCoreSMTLIBService {

	private final String z3Command;

	/**
	 * Execution Time of the service.
	 */
	private long timeConsumption = 0;
	private long satTimeConsumption = 0;
	private long unsatTimeConsumption = 0;

	public ModelCoreZ3Service(Green solver, Properties properties) {
		super(solver);
		String p = properties.getProperty("green.z3.path");
		String a = properties.getProperty("green.z3.args");
		z3Command = p + ' ' + a;
	}

	@Override
	protected ModelCore solve0(String smtQuery, Map<Variable, String> variables,
			Map<String, Expression> coreClauseMapping) {
		long startTime = System.currentTimeMillis();
		try {
			Process process = Runtime.getRuntime().exec(z3Command);
			OutputStream stdin = process.getOutputStream();
			InputStream stdout = process.getInputStream();
			BufferedReader outReader = new BufferedReader(new InputStreamReader(stdout));
			stdin.write((smtQuery + "\n").getBytes());
			stdin.flush();
			String output = outReader.readLine();

			boolean issat = false;
			switch (output) {
			case "sat":
				smtQuery = "(get-model)";
				issat = true;
				break;
			case "unsat":
				smtQuery = "(get-unsat-core)";
				break;
			default:
				log.fatal("Z3 returned a null: " + output);
				return null;
			}

			stdin.write((smtQuery + "(exit)\n").getBytes());
			stdin.flush();
			stdin.close();
			output = outReader.lines().collect(Collectors.joining());
			stdout.close();
			process.destroy();

			ModelCore tmp;
			if (issat) {
				tmp = retrieveModel(output, variables);
				satTimeConsumption += (System.currentTimeMillis() - startTime);
			} else {
				tmp = retrieveCore(output, coreClauseMapping);
				unsatTimeConsumption += (System.currentTimeMillis() - startTime);
			}
			timeConsumption += (System.currentTimeMillis() - startTime);
			return tmp;
		} catch (IOException x) {
			log.log(Level.FATAL, x.getMessage(), x);
		}
		return null;
	}

	private ModelCore retrieveModel(String output, Map<Variable, String> variables) {
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

		HashMap<Variable, Constant> model = new HashMap<>();
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
		return new ModelCore(true, model, null);
	}

	private ModelCore retrieveCore(String output, Map<String, Expression> coreClauseMapping) {
		String[] clauseNames = output.replaceAll("^\\s*\\(\\s*([^\\s].*[^\\s]*)\\s*\\)\\s*$", "$1").split("\\s+");
		Set<Expression> clauses = new HashSet<>();
		for (String namedClause : clauseNames) {
			Expression realClause = coreClauseMapping.get(namedClause);
			if (realClause != null) {
				clauses.add(realClause);
			}
		}
		return new ModelCore(false, null, clauses);
	}

	@Override
	public void report(Reporter reporter) {
//        reporter.reportZZ("cacheHitCount", cacheHitCount);
//        reporter.reportZZ("cacheMissCount", cacheMissCount);
//        reporter.reportZZ("satCacheHitCount", satHitCount);
//        reporter.reportZZ("unsatCacheHitCount", unsatHitCount);
//        reporter.reportZZ("satCacheMissCount", satMissCount);
//        reporter.reportZZ("unsatCacheMissCount", unsatMissCount);
//        reporter.reportZZ("satQueries", satCount);
//        reporter.reportZZ("unsatQueries", unsatCount);
		reporter.setContext(getClass().getSimpleName());
		reporter.report("timeConsumption", timeConsumption);
		reporter.report("satTimeConsumption", satTimeConsumption);
		reporter.report("unsatTimeConsumption", unsatTimeConsumption);
		reporter.report("storageTimeConsumption", storageTimeConsumption);
		reporter.report("translationTimeConsumption", translationTimeConsumption);
		reporter.report("conjunctCount", conjunctCount);
		reporter.report("varCount", varCount);
	}
}
