/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.taskmanager;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import org.apache.logging.log4j.Logger;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Service;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.util.Reporter;

/**
 * Parallel task manager that uses Java's {@link ExecutorService} mechanisms to
 * potentially execute services in parallel.
 */
public class ParallelTaskManager implements TaskManager {

	/**
	 * Associated GREEN solver.
	 */
	private final Green solver;

	/**
	 * Logging mechanism.
	 */
	private final Logger log;

	/**
	 * Java's {@link ExecutorService} which is essentially a pool of threads.
	 */
	private final ExecutorService executor;

	/**
	 * Number of processed requests.
	 */
	private int processedCount = 0;

	/**
	 * Number of tasks executed in total.
	 */
	private int threadsCreated = 0;

	/**
	 * Number of parallel threads.
	 */
	private int maxSimultaneousThreads = 0;

	/**
	 * Create a parallel task manager.
	 * 
	 * @param solver
	 *               associated GREEN solver
	 */
	public ParallelTaskManager(final Green solver) {
		this.solver = solver;
		log = solver.getLogger();
		executor = Executors.newCachedThreadPool();
	}

	@Override
	public Object process(final String serviceName, final Instance instance) {
		processedCount++;
		log.info("processing serviceName=\"" + serviceName + "\"");
		final Set<Service> services = solver.getService(serviceName);
		try {
			return execute(null, null, services, Collections.singleton(instance));
		} catch (InterruptedException x) {
			log.fatal("interrupted", x);
		} catch (ExecutionException x) {
			log.fatal("thread execution error", x);
		}
		return null;
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
	 * @throws InterruptedException
	 *                              if the parallel execution was interrupted
	 * @throws ExecutionException
	 *                              if a task produced an exception and its result
	 *                              is unavailable
	 */
	private Object execute(Service parent, Instance parentInstance, Set<Service> services, Set<Instance> instances)
			throws InterruptedException, ExecutionException {
		CompletionService<Object> cs = new ExecutorCompletionService<Object>(executor);
		int n = services.size() * instances.size();
		if (n > maxSimultaneousThreads) {
			maxSimultaneousThreads = n;
		}
		List<Future<Object>> futures = new ArrayList<Future<Object>>(n);
		Object result = null;
		try {
			for (Service service : services) {
				for (Instance instance : instances) {
					futures.add(cs.submit(new Task(parent, parentInstance, service, instance)));
					threadsCreated++;
				}
			}
			while ((result == null) && (n-- > 0)) {
				result = cs.take().get();
			}
		} finally {
			for (Future<Object> f : futures) {
				f.cancel(true);
			}
		}
		if (parent != null) {
			result = parent.allChildrenDone(parentInstance, result);
			if (result == null) {
				log.fatal("Should never happen! Got AllChildrenDone in PTM with NULL result");
			}
		}
		return result;
	}

	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("processedCount", processedCount);
		reporter.report("threadsCreated", threadsCreated);
		reporter.report("maxSimultaneousThreads", maxSimultaneousThreads);
	}

	/**
	 * Shutdown Java's set of threads.
	 *
	 * @see za.ac.sun.cs.green.taskmanager.TaskManager#shutdown()
	 */
	@Override
	public void shutdown() {
		executor.shutdown();
	}

	// ======================================================================
	//
	// SINGLE TASK FOR A THREAD
	//
	// ======================================================================

	/**
	 * A task to execute one service for one instance.
	 */
	private class Task implements Callable<Object> {

		/**
		 * Parent service that spawned the instance.
		 */
		private final Service parent;

		/**
		 * Parent instance that spawned the instance.
		 */
		private final Instance parentInstance;

		/**
		 * Service to execute.
		 */
		private final Service service;

		/**
		 * Instance to execute service on.
		 */
		private final Instance instance;

		/**
		 * Construct a new task.
		 * 
		 * @param parent
		 *                       parent service that spawned the instance
		 * @param parentInstance
		 *                       parent instance that spawned the instance
		 * @param service
		 *                       service to execute
		 * @param instance
		 *                       instance to execute service on
		 */
		Task(final Service parent, final Instance parentInstance, final Service service, final Instance instance) {
			this.parent = parent;
			this.parentInstance = parentInstance;
			this.service = service;
			this.instance = instance;
		}

		/**
		 * Do the work for the task: execute on service for one instance. The procedure
		 * is exactly the same as described in
		 * {@link SerialTaskManager#execute0(Service, Instance, Service, Instance)}.
		 * This method will be invoked by the Java {@link ExecutorService} when a thread
		 * becomes available.
		 *
		 * @return final result
		 * @throws Exception
		 *                   if the execution of child services on child instances
		 *                   caused a concurrency exception
		 *
		 * @see java.util.concurrent.Callable#call()
		 */
		@Override
		public Object call() throws Exception {
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

	}

}
