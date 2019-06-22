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
import za.ac.sun.cs.green.service.ModelService;

public class ModelChocoService extends ModelService {

	public ModelChocoService(Green solver) {
		super(solver);
	}

	@Override
	protected HashMap<Variable, Object> model(Instance instance) {
		Model chocoModel = new Model();
		Map<Variable, IntVar> variableMap = new HashMap<Variable, IntVar>();
		HashMap<Variable, Object> results = new HashMap<Variable, Object>();

		try {
			new ChocoTranslator(chocoModel, variableMap).translate(instance.getExpression());
			Solver chocoSolver = chocoModel.getSolver();
			if (!chocoSolver.solve()) {
				log.warn("constraint has no model, it is infeasible");
				return null;
			}
			for (Map.Entry<Variable, IntVar> entry : variableMap.entrySet()) {
				Variable greenVar = entry.getKey();
				IntVar chocoVar = entry.getValue();
				Object val = chocoVar.getValue();
				results.put(greenVar, val);
				String logMessage = "" + greenVar + " has value " + val;
				log.info(logMessage);
			}
			return results;
		} catch (TranslatorUnsupportedOperation x) {
			log.warn(x.getMessage(), x);
		} catch (VisitorException x) {
			log.fatal("encountered an exception -- this should not be happening!", x);
		}
		return null;
	}

}
