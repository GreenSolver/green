package za.ac.sun.cs.green.service.z3;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.*;
import za.ac.sun.cs.green.service.smtlib.ModelCoreSMTLIBService;
import za.ac.sun.cs.green.util.Reporter;

import java.io.*;
import java.util.*;
import java.util.stream.Collectors;

import org.apache.logging.log4j.Level;

public class ModelCoreZ3Service extends ModelCoreSMTLIBService {
	private final String DEFAULT_Z3_PATH;
	private final String DEFAULT_Z3_ARGS = "-smt2 -in";

	private final String z3Command;
	private final String resourceName = "build.properties";

	/**
	 * Execution Time of the service.
	 */
	private long timeConsumption = 0;
	private long satTimeConsumption = 0;
	private long unsatTimeConsumption = 0;

	public ModelCoreZ3Service(Green solver, Properties properties) {
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

        String z3Path = "/z3/build/z3";
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
            }
            resourceStream.close();
        } catch (IOException x) {
            // ignore
        }

        DEFAULT_Z3_PATH = z3Path;

		String p = properties.getProperty("green.z3.path", DEFAULT_Z3_PATH);
		String a = properties.getProperty("green.z3.args", DEFAULT_Z3_ARGS);
		z3Command = p + ' ' + a;
	}

	@Override
	protected ModelCore solve0(String smtQuery, Map<Variable, String> variables, Map<String, Expression> coreClauseMapping) {
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
				} else if (var instanceof IntegerVariable) {
					String val = assignment.get(name);
					val = val.replaceAll("\\(\\s*-\\s*(.+)\\)", "-$1");
					value = new IntegerConstant(Long.parseLong(val), ((IntegerVariable) var).getSize());
				} else if (var instanceof RealVariable) {
                    value = new RealConstant(Double.parseDouble(assignment.get(name)));
                }
		        if (value != null) {
                    model.put(var, value);
                }
            }
        }
		return new ModelCore(true, model,null);
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
//        reporter.report(getClass().getSimpleName(), "cacheHitCount = " + cacheHitCount);
//        reporter.report(getClass().getSimpleName(), "cacheMissCount = " + cacheMissCount);
//        reporter.report(getClass().getSimpleName(), "satCacheHitCount = " + satHitCount);
//        reporter.report(getClass().getSimpleName(), "unsatCacheHitCount = " + unsatHitCount);
//        reporter.report(getClass().getSimpleName(), "satCacheMissCount = " + satMissCount);
//        reporter.report(getClass().getSimpleName(), "unsatCacheMissCount = " + unsatMissCount);
//        reporter.report(getClass().getSimpleName(), "satQueries = " + satCount);
//        reporter.report(getClass().getSimpleName(), "unsatQueries = " + unsatCount);
        reporter.report(getClass().getSimpleName(), "timeConsumption = " + timeConsumption);
        reporter.report(getClass().getSimpleName(), "satTimeConsumption = " + satTimeConsumption);
        reporter.report(getClass().getSimpleName(), "unsatTimeConsumption = " + unsatTimeConsumption);
        reporter.report(getClass().getSimpleName(), "storageTimeConsumption = " + storageTimeConsumption);
        reporter.report(getClass().getSimpleName(), "translationTimeConsumption = " + translationTimeConsumption);
        reporter.report(getClass().getSimpleName(), "conjunctCount = " + conjunctCount);
        reporter.report(getClass().getSimpleName(), "varCount = " + varCount);
	}
}
