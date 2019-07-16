package za.ac.sun.cs.green.service.z3;

import java.util.Properties;

import za.ac.sun.cs.green.Green;

/**
 * Z3 command-line SAT service.
 */
public class SATZ3RealService extends SATZ3Service {

	/**
	 * Construct an instance of the Z3 command-line service.
	 * 
	 * @param solver     associated Green solver
	 * @param properties properties used to construct the service
	 */
	public SATZ3RealService(Green solver, Properties properties) {
		super(solver, properties);
	}

	/**
	 * Return the linear real arithmetic logic to be used for the solver.
	 *
	 * @return solver logic
	 */
	protected String getLogic() {
		return "QF_LRA";
	}

}
