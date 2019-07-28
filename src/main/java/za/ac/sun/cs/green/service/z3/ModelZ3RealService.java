/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.z3;

import java.util.Properties;

import za.ac.sun.cs.green.Green;

/**
 * Z3 command-line model service with real constraints.
 */
public class ModelZ3RealService extends ModelZ3Service {

	/**
	 * Construct an instance of the Z3 command-line service.
	 * 
	 * @param solver     associated Green solver
	 * @param properties properties used to construct the service
	 */
	public ModelZ3RealService(Green solver, Properties properties) {
		super(solver, properties);
	}
	
	/**
	 * Return the linear real arithmetic logic to be used for the solver.
	 *
	 * @return solver logic
	 */
	protected String getLogic() {
		return "AUFLIRA";
	}

}
