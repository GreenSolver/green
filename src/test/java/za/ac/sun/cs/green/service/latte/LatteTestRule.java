/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.latte;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.Properties;

import org.junit.AssumptionViolatedException;
import org.junit.rules.TestRule;
import org.junit.runner.Description;
import org.junit.runners.model.Statement;

import za.ac.sun.cs.green.Green;

/**
 * Rule to check if LattE {@code count} is available.
 */
public class LatteTestRule implements TestRule {

	/**
	 * Combination of the LattE executable, options, and the filename, all separated
	 * by spaces.
	 */
	private final boolean latteIsAvailable;

	/**
	 * Initialize the test rule by checking if LattE is available.
	 *
	 * @param solver associated Green solver
	 */
	public LatteTestRule(Green solver) {
		Properties properties = solver.getProperties();
		String output = "";
		try {
			String latteCommand = properties.getProperty("green.latte.path") + " --help\n";
			Process process = Runtime.getRuntime().exec(latteCommand);
			InputStream stderr = process.getErrorStream();
			BufferedReader outReader = new BufferedReader(new InputStreamReader(stderr));
			output = outReader.readLine();
			stderr.close();
			process.destroy();
		} catch (IOException x) {
			solver.getLogger().fatal(x.getMessage(), x);
		}
		latteIsAvailable = output.contains("This is LattE");
	}

	/**
	 * Check if LattE is available: if so, evaluate the test statement or otherwise
	 * throw an exception.
	 *
	 * @param base        {@link Statement} to be modified
	 * @param description {@link Description} of the test implemented in base
	 * @return a new statement that evaluates the statement or throws an exception
	 * 
	 * @see org.junit.rules.TestRule#apply(org.junit.runners.model.Statement,
	 *      org.junit.runner.Description)
	 */
	@Override
	public Statement apply(Statement base, Description description) {
		return new Statement() {
			@Override
			public void evaluate() throws Throwable {
				if (!isLatteAvailable()) {
					throw new AssumptionViolatedException("Cannot detect LattE.  Skipping test!");
				} else {
					base.evaluate();
				}
			}
		};
	}

	/**
	 * Check if LattE is available.
	 *
	 * @return {@code true} if and only if LattE is available
	 */
	protected boolean isLatteAvailable() {
		return latteIsAvailable;
	}

}
