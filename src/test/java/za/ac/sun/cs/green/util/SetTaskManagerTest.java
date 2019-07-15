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

import java.util.Properties;

import org.junit.Test;

import za.ac.sun.cs.green.Green;

/**
 * Test that the task manager is set correctly.
 */
public class SetTaskManagerTest {

	/**
	 * Check that setting {@link DummyTaskManager} in the configuration properties
	 * is correctly passed to a Green solver.
	 *
	 * @result Green solver should return the correct task manager instance
	 */
	@Test
	public void test01() {
		Green solver = new Green("GREEN-TEST");
		Properties props = new Properties();
		props.setProperty("green.taskmanager", DummyTaskManager.class.getCanonicalName());
		Configuration config = new Configuration(solver, props);
		config.configure();
		assertEquals(DummyTaskManager.class, solver.getTaskManager().getClass());
	}

}
