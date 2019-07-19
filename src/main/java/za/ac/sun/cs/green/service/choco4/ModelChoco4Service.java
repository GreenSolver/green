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

import org.chocosolver.solver.Solver;
import org.chocosolver.solver.variables.IntVar;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.service.ModelService;
import za.ac.sun.cs.green.service.ModelService.Model;

/**
 * Choco4 model service.
 */
public class ModelChoco4Service extends ModelService {

	/**
	 * Construct an instance of the Choco4 model service.
	 * 
	 * @param solver
	 *               associated GREEN solver
	 */
	public ModelChoco4Service(Green solver) {
		super(solver);
	}

	/**
	 * Encode the problem in Choco4 and solve it.
	 *
	 * @param instance
	 *                 problem to solve
	 * @return result of the computation as a {@link Model}
	 *
	 * @see za.ac.sun.cs.green.service.ModelService#model(za.ac.sun.cs.green.Instance)
	 */
	@Override
	protected Model model(Instance instance) {
		try {
			org.chocosolver.solver.Model chocoModel = new org.chocosolver.solver.Model();
			Map<Variable, IntVar> variableMap = new HashMap<>();
			new ChocoTranslator(log, chocoModel, variableMap).translate(instance.getExpression());
			Solver chocoSolver = chocoModel.getSolver();
			if (!chocoSolver.solve()) {
				log.warn("constraint has no model, it is infeasible");
				return new ModelService.Model(false, null);
			}
			Map<Variable, Constant> model = new HashMap<>();
			for (Map.Entry<Variable, IntVar> entry : variableMap.entrySet()) {
				model.put(entry.getKey(), new IntConstant(entry.getValue().getValue()));
			}
			log.trace("model: {}", model);
			return new Model(true, model);
		} catch (TranslatorUnsupportedOperation x) {
			log.warn(x.getMessage(), x);
		} catch (VisitorException x) {
			log.fatal("encountered an exception -- this should not be happening!", x);
		}
		return null;
	}

}
