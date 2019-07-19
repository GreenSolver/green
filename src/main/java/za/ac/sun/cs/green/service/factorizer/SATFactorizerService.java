/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.factorizer;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Service;

/**
 * Factorizer service that handles SAT queries.
 */
public class SATFactorizerService extends FactorizerService {

	/**
	 * Constructor for the SAT factorizer service.
	 * 
	 * @param solver
	 *               the {@link Green} solver this service will be added to
	 */
	public SATFactorizerService(Green solver) {
		super(solver);
	}

	/**
	 * Handle a partial result (for a single factor). This amounts to returning a
	 * "{@code false}" result as soon as a factor is not satisfiable.
	 *
	 * @param instance
	 *                    input instance
	 * @param subservice
	 *                    subservice (= child service) that computed a result
	 * @param subinstance
	 *                    subinstance which this service passed to the subservice
	 * @param result
	 *                    result return by the sub-service
	 * @return a new (intermediary) result
	 *
	 * @see za.ac.sun.cs.green.service.factorizer.FactorizerService#childDone(za.ac.sun.cs.green.Instance,
	 *      za.ac.sun.cs.green.Service, za.ac.sun.cs.green.Instance,
	 *      java.lang.Object)
	 */
	@Override
	public Object childDone(Instance instance, Service subservice, Instance subinstance, Object result) {
		if (result instanceof Boolean) {
			if (!(Boolean) result) {
				return Boolean.FALSE;
			}
		}
		return super.childDone(instance, subservice, subinstance, result);
	}

}
