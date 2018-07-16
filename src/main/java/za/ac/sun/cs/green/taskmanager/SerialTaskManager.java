package za.ac.sun.cs.green.taskmanager;

import java.util.Collections;
import java.util.Set;

import org.apache.logging.log4j.Logger;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Service;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.util.Reporter;

public class SerialTaskManager implements TaskManager {

	private final Green solver;

	private final Logger LOGGER;

	private int processedCount = 0;

	public SerialTaskManager(final Green solver) {
		this.solver = solver;
		LOGGER = solver.getLogger();
	}

	public Object execute(Service parent, Instance parentInstance, Set<Service> services, Set<Instance> instances) {
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

	public Object execute0(Service parent, Instance parentInstance, Service service, Instance instance) {
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
	public Object process(final String serviceName, final Instance instance) {
		LOGGER.info("processing serviceName=\"" + serviceName + "\"");
		processedCount++;
		final Set<Service> services = solver.getService(serviceName);
		return execute(null, null, services, Collections.singleton(instance));
	}

	@Override
	public void report(Reporter reporter) {
		reporter.report(getClass().getSimpleName(), "processedCount = " + processedCount);
	}

	@Override
	public void shutdown() {
	}

}
