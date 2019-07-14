/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.factorizer;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Service;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.service.ModelService.Model;

/**
 * Factorizer service that handles SAT queries.
 */
public class ModelFactorizerService extends FactorizerService {

	/**
	 * Satellite data key for collected models for factors.
	 */
	public static final String FACTOR_MODELS = "FACTOR_MODELS";

	/**
	 * Constructor for the model factorizer service.
	 *
	 * @param solver the {@link Green} solver this service will be added to
	 */
	public ModelFactorizerService(Green solver) {
		super(solver);
	}

	/**
	 * Process a request (in addition to whatever the {@link Factorizer} superclass
	 * does) by creating a satellite data item where the model for all of the
	 * factors is stored.
	 *
	 * @param instance the instance to factorize
	 * @return set of factors as instances
	 *
	 * @see za.ac.sun.cs.green.service.factorizer.FactorizerService#processRequest0(za.ac.sun.cs.green.Instance)
	 */
	@Override
	protected Set<Instance> processRequest0(Instance instance) {
		instance.setData(FACTOR_MODELS, new HashMap<Variable, Object>());
		return super.processRequest0(instance);
	}

	/**
	 * Handle a partial result (for a single factor). This amounts to returning a
	 * "{@code false}" result as soon as a factor is not satisfiable.
	 *
	 * @param instance    input instance
	 * @param subService  subservice (= child service) that computed a result
	 * @param subInstance subinstance which this service passed to the subservice
	 * @param result      result return by the sub-service
	 * @return a new (intermediary) result
	 *
	 * @see za.ac.sun.cs.green.service.factorizer.FactorizerService#childDone(za.ac.sun.cs.green.Instance,
	 *      za.ac.sun.cs.green.Service, za.ac.sun.cs.green.Instance,
	 *      java.lang.Object)
	 */
	@Override
	public Object childDone(Instance instance, Service subservice, Instance subinstance, Object result) {
		if (result instanceof Model) {
			if (!((Model) result).isSat()) {
				return result;
			}
		}
		return super.childDone(instance, subservice, subinstance, result);
	}

	/**
	 * Handle a new result by merging its model with the model for all factors
	 * stored in the instance's satellite data.
	 *
	 * @param instance    input instance
	 * @param subService  subservice (= child service) that computed a result
	 * @param subInstance subinstance which this service passed to the subservice
	 * @param result      result return by the sub-service
	 * @return a new (intermediary) result
	 *
	 * @see za.ac.sun.cs.green.service.factorizer.FactorizerService#handleNewChild(za.ac.sun.cs.green.Instance,
	 *      za.ac.sun.cs.green.Service, za.ac.sun.cs.green.Instance,
	 *      java.lang.Object)
	 */
	@Override
	protected Object handleNewChild(Instance instance, Service subservice, Instance subinstance, Object result) {
		if (result instanceof Model) {
			@SuppressWarnings("unchecked")
			Map<Variable, Constant> model = (Map<Variable, Constant>) instance.getData(FACTOR_MODELS);
			model.putAll(((Model) result).getModel());
			return model;
		} else {
			return result;
		}
	}

}
