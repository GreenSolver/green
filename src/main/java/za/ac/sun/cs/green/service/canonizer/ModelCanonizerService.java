/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.canonizer;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.service.ModelService.Model;

/**
 * Canonizer service for model problems.
 */
public class ModelCanonizerService extends SATCanonizerService {

	private static final String RENAME = "RENAME";

	// ======================================================================
	//
	// CONSTRUCTOR & METHODS
	//
	// ======================================================================

	/**
	 * Create a service to canonize expressions for model queries.
	 * 
	 * @param solver
	 *               the associated Green solver
	 */
	public ModelCanonizerService(Green solver) {
		super(solver);
	}

	/**
	 * Compute the inverse of a variable to variable mapping.
	 *
	 * @param map
	 *            variable-to-variable map
	 * @return new inverse mapping
	 */
	private Map<Variable, Variable> reverseMap(Map<Variable, Variable> map) {
		Map<Variable, Variable> revMap = new HashMap<>();
		for (Map.Entry<Variable, Variable> m : map.entrySet()) {
			revMap.put(m.getValue(), m.getKey());
		}
		return revMap;
	}

	/**
	 * Process an incoming request. This checks if the instance contains satellite
	 * data for the solution, and, if not, canonizes the instance.
	 * 
	 * @param instance
	 *                 problem to solve
	 * @return singleton set with new canonized instance
	 *
	 * @see za.ac.sun.cs.green.service.canonizer.SATCanonizerService#processRequest(za.ac.sun.cs.green.Instance)
	 */
	@SuppressWarnings("unchecked")
	@Override
	public Set<Instance> processRequest(Instance instance) {
		log.trace("[{}]", instance);
		long startTime = System.currentTimeMillis();
		invocationCount++;
		Object result = instance.getData(getClass());
		if (!(result instanceof Set<?>)) {
			final Map<Variable, Variable> map = new HashMap<>();
			final Expression expression = canonize(instance.getFullExpression(), map);
			Map<Variable, Variable> reverseMap = reverseMap(map);
			final Instance newInstance = new Instance(getSolver(), instance.getSource(), null, expression);
			result = Collections.singleton(newInstance);
			instance.setData(getClass(), result);
			instance.setData(RENAME, reverseMap);
		}
		serviceTimeConsumption += (System.currentTimeMillis() - startTime);
		return (Set<Instance>) result;
	}

	/**
	 * When a model is returned, update the model to reflect the original instead of
	 * the renamed variables.
	 *
	 * @param instance
	 *                 the input instance
	 * @param result
	 *                 the result computed so far by this service
	 * @return the final result
	 *
	 * @see za.ac.sun.cs.green.service.BasicService#allChildrenDone(za.ac.sun.cs.green.Instance,
	 *      java.lang.Object)
	 */
	@Override
	public Object allChildrenDone(Instance instance, Object result) {
		Object map = instance.getData(RENAME);
		if ((result instanceof Model) && (map instanceof Map<?, ?>)) {
			Model model = (Model) result;
			@SuppressWarnings("unchecked")
			Map<Variable, Variable> reverseMap = (Map<Variable, Variable>) map;
			Map<Variable, Constant> newMap = new HashMap<>();
			for (Map.Entry<Variable, Constant> e : model.getModel().entrySet()) {
				newMap.put(reverseMap.get(e.getKey()), e.getValue());
			}
			return new Model(model.isSat(), newMap);
		} else {
			return null;
		}
	}

}
