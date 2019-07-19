/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green;

import java.util.Set;

import za.ac.sun.cs.green.util.Reporter;

/**
 * The basis interface for all services.
 */
public interface Service {

	/**
	 * Return the instance of the Green solver associated with this service.
	 * 
	 * @return instance of the Green solver associated with this service
	 */
	Green getSolver();

	/**
	 * Process an instance by (possibly) transforming it and (possibly) breaking it
	 * into one or more subinstances.
	 * 
	 * For example, the factorizer partitions the formula associated with the
	 * instance into subformulas, creates a new subinstance for each subformula, and
	 * returns this set. On the other hand, a SAT service would pass the formula to
	 * an external solver and return an empty set of subinstances.
	 * 
	 * @param instance instance to solve
	 * @return set of subinstances passed to subservices
	 */
	Set<Instance> processRequest(Instance instance);

	/**
	 * Perform an update computation based on a new subresult computed by a child
	 * service of the current service.
	 * 
	 * @param instance    input instance
	 * @param subService  subservice (i.e., child service) that computed a result
	 * @param subInstance subinstance which this service passed to the subservice
	 * @param result      result returned by the subservice
	 * @return a new (intermediary) result
	 */
	Object childDone(Instance instance, Service subService, Instance subInstance, Object result);

	/**
	 * Perform a final computation on the results computed by the children of the
	 * current service.
	 * 
	 * @param instance input instance
	 * @param result   result computed so far by this service
	 * @return final result
	 */
	Object allChildrenDone(Instance instance, Object result);

	/**
	 * Shut down the service.
	 */
	void shutdown();

	/**
	 * Report on the performance or state of the service.
	 * 
	 * @param reporter mechanism through which reporting is done
	 */
	void report(Reporter reporter);

}
