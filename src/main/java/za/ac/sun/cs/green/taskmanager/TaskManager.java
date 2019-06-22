package za.ac.sun.cs.green.taskmanager;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.util.Reporter;

public interface TaskManager {

	Object process(String serviceName, Instance instance);

	void report(Reporter reporter);

	void shutdown();
	
}
