/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.taskmanager;

import java.util.Collections;
import java.util.Set;

import org.apache.logging.log4j.Logger;

import reactor.util.annotation.Nullable;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Service;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Serial task manager that executes all actions serially.
 */
public class SerialTaskManager implements TaskManager {

	/**
	 * Associated GREEN solver.
	 */
	private final Green solver;

	/**
	 * Logging mechanism.
	 */
	private final Logger log;

	/**
	 * Number of processed requests.
	 */
	private int processedCount = 0;

	/**
	 * Create a serial task manager.
	 * 
	 * @param solver
	 *               associated GREEN solver
	 */
	public SerialTaskManager(final Green solver) {
		this.solver = solver;
		log = solver.getLogger();
	}

	@Override
	public Object process(final String serviceName, final Instance instance) {
		log.info("processing serviceName=\"" + serviceName + "\"");
		processedCount++;
		final Set<Service> services = solver.getService(serviceName);
		return execute(null, null, services, Collections.singleton(instance));
	}

	/**
	 * Execute a set of services for a set of instances. As soon as one such
	 * execution returns a non-null result, the execution phase terminates. If the
	 * parent service is not null, the final result (possibly {@code null}) is sent
	 * to the parent's {@link Service#allChildrenDone(Instance, Object)} method,
	 * which optionally changes the final result. Finally, it returns the final
	 * result.
	 *
	 * @param parent
	 *                       parent service that spawned the set of instances
	 * @param parentInstance
	 *                       parent instance that spawned the instances
	 * @param services
	 *                       current set of services to execute
	 * @param instances
	 *                       current set of instances to execute services on
	 * @return final result
	 */
	private Object execute(@Nullable Service parent, @Nullable Instance parentInstance, Set<Service> services,
			Set<Instance> instances) {
		Object result = null;
		for (Service service : services) {
			for (Instance instance : instances) {
				result = execute0(parent, parentInstance, service, instance);
				if (result != null) {
					break;
				}
			}
		}
		if (parent != null) {
			result = parent.allChildrenDone(parentInstance, result);
		}
		return result;
	}

	/**
	 * Execute one service for one instance. This comprises several steps:
	 * 
	 * <ol>
	 * 
	 * <li>The {@link Service#processRequest(Instance)} is invoked for the service
	 * to obtain a set of child instances.</li>
	 * 
	 * <li>All of the child services of the service are executed for all of the
	 * child instances.</li>
	 * 
	 * <li>If the parent service is non-null, the
	 * {@link Service#childDone(Instance, Service, Instance, Object)} method is
	 * invoked to optionally change the final result.</li>
	 * 
	 * <li>This final result is returned.</li>
	 * 
	 * </ol>
	 * 
	 * There are a number of exceptions to this procedure:
	 * 
	 * <ul>
	 * 
	 * <li>If the set of child instances is {@code null} or empty,
	 * {@link Service#allChildrenDone(Instance, Object)} method is first invoked to
	 * optionally modify the result (which is {@code null}).</li>
	 * 
	 * <li>Otherwise, if the set of child services is {@code null} or empty,
	 * {@link Service#allChildrenDone(Instance, Object)} method is first invoked to
	 * optionally modify the result (which is {@code null}).</li>
	 * 
	 * <li>Otherwise, the {@link #execute(Service, Instance, Set, Set)} method is
	 * invoked to execute all the child services on all the child instances.</li>
	 * 
	 * </ul>
	 *
	 * @param parent
	 *                       parent service that spawned the instance
	 * @param parentInstance
	 *                       parent instance that spawned the instance
	 * @param services
	 *                       service to execute
	 * @param instances
	 *                       instance to execute service on
	 * @return final result
	 */
	Object execute0(Service parent, Instance parentInstance, Service service, Instance instance) {
		Object result = null;
		Set<Instance> subinstances = service.processRequest(instance);
		if ((subinstances != null) && (subinstances.size() > 0)) {
			Set<Service> subservices = solver.getService(service);
			if ((subservices != null) && (subservices.size() > 0)) {
				result = execute(service, instance, subservices, subinstances);
			} else {
				result = service.allChildrenDone(instance, result);
			}
		} else {
			result = service.allChildrenDone(instance, result);
		}
		if (parent != null) {
			result = parent.childDone(parentInstance, service, instance, result);
		}
		return result;
	}

	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("processedCount", processedCount);
	}

	/**
	 * Do nothing.
	 *
	 * @see za.ac.sun.cs.green.taskmanager.TaskManager#shutdown()
	 */
	@Override
	public void shutdown() {
	}

}
