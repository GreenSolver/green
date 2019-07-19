/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.util;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.taskmanager.TaskManager;

/**
 * Do-nothing task manager for use in tests.
 */
public class DummyTaskManager implements TaskManager {

	/**
	 * Construct the dummy task manager.
	 * 
	 * @param solver {@link Green} solver this task manager will be added to
	 */
	public DummyTaskManager(Green solver) {
	}

	/**
	 * Handle a service request for a given instance.
	 *
	 * @param serviceName name of the service to apply
	 * @param instance    {@link Instance} to apply service to
	 * @return always {@code null}
	 * 
	 * @see za.ac.sun.cs.green.taskmanager.TaskManager#process(java.lang.String,
	 *      za.ac.sun.cs.green.Instance)
	 */
	@Override
	public Object process(String serviceName, Instance instance) {
		return null;
	}

	/**
	 * Report nothing
	 *
	 * @param reporter reporting mechanism
	 * @see za.ac.sun.cs.green.taskmanager.TaskManager#report(za.ac.sun.cs.green.util.Reporter)
	 */
	@Override
	public void report(Reporter reporter) {
	}

	/**
	 * Shut down the task manager (by doing nothing).
	 *
	 * @see za.ac.sun.cs.green.taskmanager.TaskManager#shutdown()
	 */
	@Override
	public void shutdown() {
	}

}
