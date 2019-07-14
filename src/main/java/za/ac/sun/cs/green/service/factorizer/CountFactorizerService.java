/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.factorizer;

import java.util.Set;

import org.apfloat.Apint;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Service;

/**
 * Factorizer service that handles count queries.
 */
public class CountFactorizerService extends FactorizerService {

	/**
	 * Satellite data key for the accumulated for factors.
	 */
	public static final String FACTOR_COUNT = "FACTOR_COUNT";

	/**
	 * Constructor for the count factorizer service.
	 *
	 * @param solver the {@link Green} solver this service will be added to
	 */
	public CountFactorizerService(Green solver) {
		super(solver);
	}

	/**
	 * Process a request (in addition to whatever the {@link Factorizer} superclass
	 * does) by creating a satellite data item where the total count for the factors
	 * is stored.
	 *
	 * @param instance the instance to factorize
	 * @return set of factors as instances
	 *
	 * @see za.ac.sun.cs.green.service.factorizer.FactorizerService#processRequest0(za.ac.sun.cs.green.Instance)
	 */
	@Override
	protected Set<Instance> processRequest0(Instance instance) {
		instance.setData(FACTOR_COUNT, Apint.ONE);
		return super.processRequest0(instance);
	}

	/**
	 * Handle a partial result (for a single factor). This amounts to returning 0 as
	 * soon as a factor is not satisfiable.
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
		if (result instanceof Apint) {
			if (!((Apint) result).equals(Apint.ZERO)) {
				return Apint.ZERO;
			}
		}
		return super.childDone(instance, subservice, subinstance, result);
	}

	/**
	 * Handle a new result by multiplying its (independent) count with the
	 * accumulated overall count for factors.
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
		if (result instanceof Apint) {
			Apint newCount = ((Apint) instance.getData(FACTOR_COUNT)).multiply((Apint) result);
			instance.setData(FACTOR_COUNT, newCount);
			return newCount;
		} else {
			return result;
		}
	}

}
