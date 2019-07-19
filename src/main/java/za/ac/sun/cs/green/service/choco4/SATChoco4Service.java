/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.choco4;

import java.util.HashMap;
import java.util.Map;

import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.variables.IntVar;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.service.SATService;

/**
 * Choco4 SAT service.
 */
public class SATChoco4Service extends SATService {

	/**
	 * Construct an instance of the Choco4 SAT service.
	 * 
	 * @param solver
	 *               associated Green solver
	 */
	public SATChoco4Service(Green solver) {
		super(solver);
	}

	/**
	 * Encode the problem in Choco4 and solve it.
	 *
	 * @param instance
	 *                 problem to solve
	 * @return {@code true} mean SAT, {@code false} mean UNSAT, {@code null} means
	 *         Choco4 cannot solve the problem
	 *
	 * @see za.ac.sun.cs.green.service.SATService#solve(za.ac.sun.cs.green.Instance)
	 */
	@Override
	protected Boolean solve(Instance instance) {
		Model chocoModel = new Model();
		Map<Variable, IntVar> variableMap = new HashMap<Variable, IntVar>();
		try {
			log.debug("solve: {}", () -> instance.getFullExpression());
			new ChocoTranslator(log, chocoModel, variableMap).translate(instance.getFullExpression());
			Solver chocoSolver = chocoModel.getSolver();
			return chocoSolver.solve();
		} catch (TranslatorUnsupportedOperation x) {
			log.warn(x.getMessage(), x);
		} catch (VisitorException x) {
			log.fatal("encountered an exception -- this should not be happening!", x);
		}
		return null;
	}
}
