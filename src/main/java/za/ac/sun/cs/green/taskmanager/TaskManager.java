/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.taskmanager;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Interface for all task managers.
 */
public interface TaskManager {

	/**
	 * Process a request to execute a named service on a given instance.
	 *
	 * @param serviceName name of service to execute
	 * @param instance instance to execute service on
	 * @return result of the execution
	 */
	Object process(String serviceName, Instance instance);

	/**
	 * Report on the behaviour of the task manager.
	 *
	 * @param reporter reporting mechanism
	 */
	void report(Reporter reporter);

	/**
	 * Shut down the task manager.
	 */
	void shutdown();
	
}
