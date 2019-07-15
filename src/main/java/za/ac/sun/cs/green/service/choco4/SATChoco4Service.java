package za.ac.sun.cs.green.service.choco4;

import java.util.HashMap;
import java.util.Map;

import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.variables.IntVar;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.service.SATService;

public class SATChoco4Service extends SATService {

	public SATChoco4Service(Green solver) {
		super(solver);
	}

	@Override
	protected Boolean solve(Instance instance) {
		Model chocoModel = new Model();
		Map<Variable, IntVar> variableMap = new HashMap<Variable, IntVar>();
		try {
			log.debug("solve: {}", () -> instance.getFullExpression());
			new ChocoTranslator(log, chocoModel, variableMap).translate(instance.getFullExpression());
			Solver chocoSolver = chocoModel.getSolver();
			return chocoSolver.solve();
		} catch (TranslatorUnsupportedOperation x) {
			log.warn(x.getMessage(), x);
		} catch (VisitorException x) {
			log.fatal("encountered an exception -- this should not be happening!", x);
		}
		return null;
	}
}
