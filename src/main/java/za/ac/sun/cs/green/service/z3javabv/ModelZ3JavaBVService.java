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
import com.microsoft.z3.Expr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.RealConstant;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.service.ModelService;
import za.ac.sun.cs.green.service.ModelService.Model;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Z3 Java library model service using bitvectors for linear integer
 * constraints.
 */
public class ModelZ3JavaBVService extends ModelService {

	/**
	 * Logic used for the Z3 solver.
	 */
	protected static final String Z3_LOGIC = "QF_BV";

	/**
	 * Size of bitvectors.
	 */
	protected static final int BV_SIZE = 32;

	/**
	 * Instance of the Z3 solver.
	 */
	protected final Solver z3Solver;

	/**
	 * Context of the Z3 solver.
	 */
	protected final Context z3Context;

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
	 * @param solver
	 *                   associated Green solver
	 * @param properties
	 *                   properties used to construct the service
	 */
	public ModelZ3JavaBVService(Green solver, Properties properties) {
		super(solver);
		Map<String, String> cfg = new HashMap<>();
		cfg.put("model", "true");
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
	 * @return a {@link Model} result or {@code null} if no answer is available
	 *
	 * @see za.ac.sun.cs.green.service.ModelService#model(za.ac.sun.cs.green.Instance)
	 */
	@Override
	protected ModelService.Model model(Instance instance) {
		long startTime = System.currentTimeMillis();

		// translate instance to Z3
		long startTime0 = System.currentTimeMillis();
		Z3JavaBVTranslator translator = new Z3JavaBVTranslator(z3Context, BV_SIZE);
		try {
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
		Map<Variable, Constant> results = new HashMap<>();
		try {
			if (Status.SATISFIABLE == z3Solver.check()) {
				Map<Variable, Expr> variableMap = translator.getVariableMap();
				com.microsoft.z3.Model model = z3Solver.getModel();
				for (Map.Entry<Variable, Expr> entry : variableMap.entrySet()) {
					Variable var = entry.getKey();
					Expr z3Var = entry.getValue();
					Expr z3Val = model.evaluate(z3Var, false);
					Constant val = null;
					if (z3Val.isIntNum()) {
						val = new IntConstant(Integer.parseInt(z3Val.toString()));
					} else if (z3Val.isRatNum()) {
						String z3ValString = z3Val.toString();
						if (z3ValString.contains("/")) {
							String[] rat = z3ValString.split("/");
							double num = Double.parseDouble(rat[0]);
							double den = Double.parseDouble(rat[1]);
							val = new RealConstant(num / den);
						} else {
							val = new RealConstant(Double.parseDouble(z3ValString));
						}
					} else if (z3Val.isBV()) {
						val = new IntConstant(Integer.parseInt(z3Val.toString()));
					} else {
						log.warn("Error unsupported type for variable {}", z3Val);
						return null;
					}
					results.put(var, val);
				}
			} else {
				unsatTimeConsumption += System.currentTimeMillis() - startTime;
				timeConsumption += System.currentTimeMillis() - startTime;
				return new ModelService.Model(false, null);
			}
		} catch (Z3Exception x) {
			log.warn("Error in Z3 ({})", x.getMessage());
		}
		satTimeConsumption += System.currentTimeMillis() - startTime;
		timeConsumption += System.currentTimeMillis() - startTime;
		return new ModelService.Model(true, results);
	}

}
