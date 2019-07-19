/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.identity;

import java.util.Collections;
import java.util.Set;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.service.BasicService;

/**
 * A service that simply passes the requests (or results) it receives unchanged
 * to its children (or parent).
 */
public class IdentityService extends BasicService {

	/**
	 * Create an instance of the identity service.
	 * 
	 * @param solver the {@link Green} solver this service will be added to
	 */
	public IdentityService(Green solver) {
		super(solver);
	}

	/**
	 * Return a singleton set that contains the incoming instance. The result of
	 * this is that requests are simply passed unchanged to children. The default
	 * implementations of {@link BasicService} will do the opposite: pass results
	 * unchanged to the parent of this service.
	 *
	 * @param instance the input instance
	 * @return a singleton set that contains {@code instance}
	 * @see za.ac.sun.cs.green.service.BasicService#processRequest(za.ac.sun.cs.green.Instance)
	 */
	@Override
	public Set<Instance> processRequest(Instance instance) {
		return Collections.singleton(instance);
	}

}
