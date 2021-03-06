/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
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
 * Z3 command-line SAT service for linear integer constraints.
 */
public class SATZ3Service extends SATSMTLIBService {

	/**
	 * The command to invoke Z3.
	 */
	protected final String z3Command;

	// ======================================================================
	//
	// TIME CONSUMPTION
	//
	// ======================================================================

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
	 * @param solver
	 *                   associated Green solver
	 * @param properties
	 *                   properties used to construct the service
	 */
	public SATZ3Service(Green solver, Properties properties) {
		super(solver);
		String p = properties.getProperty("green.z3.path");
		String a = properties.getProperty("green.z3.args");
		z3Command = p + ' ' + a;
	}

	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("timeConsumption", timeConsumption);
		reporter.report("  satTimeConsumption", satTimeConsumption);
		reporter.report("  unsatTimeConsumption", unsatTimeConsumption);
		super.report(reporter);
	}

	/**
	 * Create a subprocess to run Z3, pass the query to the process, and collect and
	 * parse the output.
	 *
	 * @param smtQuery
	 *                 translated query as SMTLIB string
	 * @return boolean result, {@code true} if and only if the query is satisfiable
	 *
	 * @see za.ac.sun.cs.green.service.smtlib.SATSMTLIBService#resolve(java.lang.String)
	 */
	@Override
	protected Boolean resolve(String smtQuery) {
		log.trace("smtQuery: {}", smtQuery);
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
