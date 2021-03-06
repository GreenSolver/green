/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green;

import java.lang.management.ManagementFactory;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import za.ac.sun.cs.green.store.NullStore;
import za.ac.sun.cs.green.store.Store;
import za.ac.sun.cs.green.taskmanager.SerialTaskManager;
import za.ac.sun.cs.green.taskmanager.TaskManager;
import za.ac.sun.cs.green.util.Pair;
import za.ac.sun.cs.green.util.Reporter;

/**
 * An instance of Green acts as a manager for services and problem instances. In
 * other words, each service is associated with an instance of a Green solver,
 * and likewise for problem instances. One software system may, if it wishes,
 * have more than Green instance. However, their services and problems are
 * entirely independent are not easily interchangeable.
 */
public class Green {

	/**
	 * The name of this solver. This is used mainly for naming the logger.
	 */
	private final String solverName;

	/**
	 * The logger for this solver.
	 */
	private final Logger log;

	/**
	 * The task manager that handles how requests are processed.
	 */
	private TaskManager taskManager;

	/**
	 * A mapping from service names to services.
	 */
	private final Map<String, Set<Service>> services0;

	/**
	 * A mapping from services to sub-services.
	 */
	private final Map<Service, Set<Service>> services1;

	/**
	 * The store associated with this Green solver.
	 */
	private Store store;

	/**
	 * Properties that may be passed down to components.
	 */
	private Properties properties = null;

	/**
	 * Constructs a Green solver instance with the given name. The name can be
	 * anything whatsoever and is mainly used to obtain a unique logger.
	 *
	 * @param solverName name of the solver
	 */
	public Green(String solverName, Logger logger) {
		this.solverName = solverName;
		this.log = logger;
		taskManager = new SerialTaskManager(this);
		store = new NullStore(this);
		services0 = new HashMap<>();
		services1 = new HashMap<>();
	}

	/**
	 * Constructs a Green solver instance with the given name. The name can be
	 * anything whatsoever and is mainly used to obtain a unique logger.
	 *
	 * @param solverName name of the solver
	 */
	public Green(String solverName) {
		this(solverName, LogManager.getLogger(solverName));
	}

	/**
	 * Constructs an anonymous -- but unique -- instance of a Green solver with a
	 * specified logger.
	 *
	 * @param logger {@link Logger} to use
	 */
	public Green(Logger logger) {
		this(ManagementFactory.getRuntimeMXBean().getName(), logger);
	}

	/**
	 * Constructs an anonymous -- but unique -- instance of a Green solver.
	 */
	public Green() {
		this(ManagementFactory.getRuntimeMXBean().getName(),
				LogManager.getLogger(ManagementFactory.getRuntimeMXBean().getName()));
	}

	/**
	 * Main function in case someone tries to run this file.
	 *
	 * @param args command-line arguments
	 */
	public static void main(String[] args) {
		System.out.println("Green is a library and should not be invoked directly.");
	}

	/**
	 * Returns the name of this solver.
	 *
	 * @return name of the solver
	 */
	public String getSolverName() {
		return solverName;
	}

	/**
	 * Returns the {@link Logger} associated with this Green instance.
	 *
	 * @return the logger of this Green instances
	 */
	public Logger getLogger() {
		return log;
	}

	/**
	 * Sets a {@link TaskManager} for this Green solver instance. By default, a new
	 * {@link SerialTaskManager} is created for a new Green solver instance.
	 *
	 * @param taskManager new task manager
	 */
	public void setTaskManager(final TaskManager taskManager) {
		this.taskManager = taskManager;
	}

	/**
	 * Returns the current {@link TaskManager} associated with this Green solver
	 * instance.
	 *
	 * @return current task manager
	 */
	public TaskManager getTaskManager() {
		return taskManager;
	}

	/**
	 * Sets a {@link Store} for this Green solver instance. By default, a
	 * {@link NullStore} is created for a new Green solver instance.
	 *
	 * @param store new store
	 */
	public void setStore(final Store store) {
		this.store = store;
	}

	/**
	 * Returns the current {@link Store} associated with this Green solver instance.
	 *
	 * @return current store
	 */
	public Store getStore() {
		return store;
	}

	/**
	 * Returns the set of {@link Service}s associated with the given service name.
	 * This mechanism allows problem instances to issue a request for a named,
	 * high-level service such as "sat". The task manager takes care of the applying
	 * the services - and their subservices - to the problem instance.
	 *
	 * @param serviceName name of a service
	 * @return set of {@link Service}s associated with the given name
	 */
	public Set<Service> getService(String serviceName) {
		return services0.get(serviceName);
	}

	/**
	 * Returns the set of sub-{@link Service}s associated with the given service.
	 * This mechanism is used by the task manager to determine the sub-services that
	 * need to be applied to a problem instance or sub-instance.
	 *
	 * @param service a service
	 * @return set of sub-{@link Service}s associated with the given service
	 */
	public Set<Service> getService(Service service) {
		return services1.get(service);
	}

	/**
	 * Associates a given service name with a given {@link Service}.
	 * <p>
	 * When clients issue a request for a Green service, this is the name they will
	 * use. So typically, it is something like "sat", "count", or "model". This
	 * really represents a meta-service that requires several other services (the
	 * slicer, the canonizer, a decision procedure, and so on) to run. The task
	 * manager takes care of this. The associated registered with this routine adds
	 * one more service to the named (meta-)service. There can be many such requests
	 * for any given name, and all of the services are recorded.
	 * <p>
	 * The usage idiom for Green is that each service passed to this routine or the
	 * {@link #registerService(Service, Service)} routine is unique.
	 *
	 * @param serviceName name of a (high-level) service
	 * @param subService  another service to associate with the name
	 */
	public void registerService(String serviceName, Service subService) {
		log.info("register service: name=\"{}\", subservice={}", serviceName, subService.getClass().getName());
		services0.computeIfAbsent(serviceName, k -> new HashSet<>()).add(subService);
	}

	/**
	 * Associates another (sub-)service with the given service. For a little more
	 * explanation, see the comments for {@link #registerService(String, Service)}.
	 *
	 * @param service    a service
	 * @param subService another service to associate with the given service
	 */
	public void registerService(Service service, Service subService) {
		log.info("register service: name=\"{}\", subservice={}", service.getClass().getName(),
				subService.getClass().getName());
		services1.computeIfAbsent(service, k -> new HashSet<>()).add(subService);
	}

	/**
	 * Dispatches a request to apply the given service to the given instance.
	 * Arbitrary services can be defined and can produce arbitrary kinds of answers.
	 * This is fully generalized so that the response is described merely as an
	 * {@link Object}.
	 *
	 * @param serviceName name of the service
	 * @param instance    problem instance
	 * @return an object that represents the Green solver's response to the request
	 */
	public Object handleRequest(String serviceName, Instance instance) {
		return taskManager.process(serviceName, instance);
	}

	/**
	 * Generates a report to the log.
	 */
	public void report() {
		final Map<String, List<String>> messages = new HashMap<>();
		final Map<String, List<Pair<String, String>>> keyValues = new HashMap<>();
		report(new Reporter() {
			@Override
			public void reportMessage(String context, String message) {
				messages.computeIfAbsent(context, k -> new ArrayList<>()).add(message);
			}

			@Override
			public void report(String context, String key, String value) {
				keyValues.computeIfAbsent(context, k -> new ArrayList<>()).add(new Pair<>(key, value));
			}
		});

		// Now write the report
		StringBuilder sb = new StringBuilder();
		for (String context : messages.keySet()) {
			sb.setLength(0);
			sb.append("=== ").append(context).append(' ');
			for (int n = 80 - sb.length(); n > 0; n--) {
				sb.append('=');
			}
			log.info("{}", sb.toString());
			for (String message : messages.get(context)) {
				log.info("  {}", message);
			}
			if (keyValues.containsKey(context)) {
				for (Pair<String, String> keyValue : keyValues.get(context)) {
					log.info("  {} == {}", keyValue.getL(), keyValue.getR());
				}
			}
		}
		for (String context : keyValues.keySet()) {
			if (messages.containsKey(context)) {
				continue;
			}
			sb.setLength(0);
			sb.append("=== ").append(context).append(' ');
			for (int n = 80 - sb.length(); n > 0; n--) {
				sb.append('=');
			}
			log.info("{}", sb.toString());
			for (Pair<String, String> keyValue : keyValues.get(context)) {
				log.info("  {} == {}", keyValue.getL(), keyValue.getR());
			}
		}
	}

	/**
	 * Generates a report using the given {@link Reporter}. This mechanism allows
	 * clients to process the report in whatever way they see fit.
	 *
	 * @param reporter {@link Reporter} for the report
	 */
	public void report(Reporter reporter) {
		taskManager.report(reporter);
		store.report(reporter);
		for (Set<Service> s : services0.values()) {
			for (Service ss : s) {
				ss.report(reporter);
			}
		}
		for (Set<Service> s : services1.values()) {
			for (Service ss : s) {
				ss.report(reporter);
			}
		}
	}

	/**
	 * Shuts down this instance of a Green solver.
	 */
	public void shutdown() {
		for (Set<Service> s : services0.values()) {
			for (Service ss : s) {
				ss.shutdown();
			}
		}
		for (Set<Service> s : services1.values()) {
			for (Service ss : s) {
				ss.shutdown();
			}
		}
		store.flushAll();
		store.shutdown();
		taskManager.shutdown();
	}

	/**
	 * Return the properties for this solver.
	 *
	 * @return current properties
	 */
	public Properties getProperties() {
		return properties;
	}

	/**
	 * Set the properties for this solver.
	 *
	 * @param properties new properties
	 */
	public void setProperties(Properties properties) {
		this.properties = properties;
	}

}
