/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.z3javabv;

import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.service.SATService;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Z3 Java library SAT service using bitvectors for linear integer constraints.
 */
public class SATZ3BVJavaService extends SATService {

	/**
	 * Logic used for the Z3 solver.
	 */
	protected static final String Z3_LOGIC = "QF_LIA";

	/**
	 * Size of bitvectors.
	 */
	protected static final int BV_SIZE = 32;
	
	/**
	 * Instance of the Z3 solver.
	 */
	protected static Solver z3Solver;

	/**
	 * Context of the Z3 solver.
	 */
	protected static Context z3Context;

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
	 * Milliseconds used to translate Green expression to Z3 library calls.
	 */
	protected long translationTimeConsumption = 0;

	/**
	 * Construct an instance of the Z3 Java library service.
	 * 
	 * @param solver     associated Green solver
	 * @param properties properties used to construct the service
	 */
	public SATZ3BVJavaService(Green solver, Properties properties) {
		super(solver);
		Map<String, String> cfg = new HashMap<>();
		cfg.put("model", "false");
		try {
			z3Context = new Context(cfg);
		} catch (Exception x) {
			x.printStackTrace();
			throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + x);
		}
		z3Solver = z3Context.mkSolver(Z3_LOGIC);
	}

	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("timeConsumption", timeConsumption);
		reporter.report("  satTimeConsumption", satTimeConsumption);
		reporter.report("  unsatTimeConsumption", unsatTimeConsumption);
		reporter.report("  translationTimeConsumption", translationTimeConsumption);
		super.report(reporter);
	}

	/**
	 * Translate the GREEN problem using Z3 library calls (by invoking the
	 * {@link Z3JavaBVTranslator}), solve the problem, and return the result.
	 *
	 * @param instance
	 *                 problem to solve
	 * @return result of the computation: {@code true} mean SAT, {@code false} mean
	 *         UNSAT, {@code null} means no answer is available
	 *
	 * @see za.ac.sun.cs.green.service.SATService#solve(za.ac.sun.cs.green.Instance)
	 */
	@Override
	protected Boolean solve(Instance instance) {
		long startTime = System.currentTimeMillis();
		Boolean result = false;

		// translate instance to Z3
		long startTime0 = System.currentTimeMillis();
		try {
			Z3JavaBVTranslator translator = new Z3JavaBVTranslator(z3Context, BV_SIZE);
			instance.getExpression().accept(translator);
			z3Solver.push();
			z3Solver.add(translator.getTranslation());
		} catch (VisitorException x) {
			log.warn("Error in translation to Z3 ({})", x.getMessage());
		} catch (Z3Exception x) {
			log.fatal("Error in Z3 ({})", x.getMessage());
		}
		translationTimeConsumption += System.currentTimeMillis() - startTime0;

		// solve
		try {
			result = (Status.SATISFIABLE == z3Solver.check());
		} catch (Z3Exception e) {
			log.warn("Error in Z3 ({})", e.getMessage());
		}

		// clean up
		int scopes = z3Solver.getNumScopes();
		if (scopes > 0) {
			z3Solver.pop(scopes);
		}
		if (result) {
			satTimeConsumption += System.currentTimeMillis() - startTime;
		} else {
			unsatTimeConsumption += System.currentTimeMillis() - startTime;
		}
		timeConsumption += System.currentTimeMillis() - startTime;
		return result;
	}

}
