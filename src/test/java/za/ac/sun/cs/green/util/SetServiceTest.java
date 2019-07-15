/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.HashSet;
import java.util.Properties;
import java.util.Set;

import org.junit.Test;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Service;
import za.ac.sun.cs.green.service.canonizer.SATCanonizerService;
import za.ac.sun.cs.green.service.choco4.SATChoco4Service;
import za.ac.sun.cs.green.service.slicer.SATSlicerService;
import za.ac.sun.cs.green.service.z3.SATZ3Service;

/**
 * Test that settings services are correctly set in the configuration
 * properties.
 */
public class SetServiceTest {

	/**
	 * Check that setting up a service pipeline in the configuration properties is
	 * correctly passed to a Green solver.
	 *
	 * @result Green solver should return the correct services for a pipeline
	 */
	@Test
	public void test() {
		// Green solver = new Green();
		Green solver = new Green("GREEN-TEST");
		Properties props = new Properties();
		props.setProperty("green.services", "sat");
		props.setProperty("green.service.sat", "(slice (canonize z3 choco))");
		props.setProperty("green.service.sat.slice", "za.ac.sun.cs.green.service.slicer.SATSlicerService");
		props.setProperty("green.service.sat.canonize", "za.ac.sun.cs.green.service.canonizer.SATCanonizerService");
		props.setProperty("green.service.sat.z3", "za.ac.sun.cs.green.service.z3.SATZ3Service");
		props.setProperty("green.service.sat.choco", "za.ac.sun.cs.green.service.choco4.SATChoco4Service");
		Configuration config = new Configuration(solver, props);
		config.configure();

		Set<Service> services = solver.getService("sat");
		Set<Class<?>> serviceClasses = classify(services);
		assertEquals(1, serviceClasses.size());
		assertTrue(serviceClasses.contains(SATSlicerService.class));

		services = solver.getService((Service) services.toArray()[0]);
		serviceClasses = classify(services);
		assertEquals(1, serviceClasses.size());
		assertTrue(serviceClasses.contains(SATCanonizerService.class));

		services = solver.getService((Service) services.toArray()[0]);
		serviceClasses = classify(services);
		assertEquals(2, serviceClasses.size());
		assertTrue(serviceClasses.contains(SATZ3Service.class));
		assertTrue(serviceClasses.contains(SATChoco4Service.class));
	}

	/**
	 * Convert a set of {@link Service} instances to the set of corresponding
	 * classes.
	 *
	 * @param services set of services
	 * @return set of corresponding classes
	 */
	private Set<Class<?>> classify(Set<Service> services) {
		Set<Class<?>> classes = new HashSet<Class<?>>();
		for (Service service : services) {
			classes.add(service.getClass());
		}
		return classes;
	}

}
