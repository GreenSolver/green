package za.ac.sun.cs.green.service.choco4;

import java.util.HashMap;
import java.util.Map;

import org.chocosolver.solver.Solver;
import org.chocosolver.solver.variables.IntVar;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.service.ModelService;

public class ModelChocoService extends ModelService {

	public ModelChocoService(Green solver) {
		super(solver);
	}

	@Override
	protected Model model(Instance instance) {
		try {
			org.chocosolver.solver.Model chocoModel = new org.chocosolver.solver.Model();
			Map<Variable, IntVar> variableMap = new HashMap<>();
			new ChocoTranslator(chocoModel, variableMap).translate(instance.getExpression());
			Solver chocoSolver = chocoModel.getSolver();
			if (!chocoSolver.solve()) {
				log.warn("constraint has no model, it is infeasible");
				return new ModelService.Model(false, null);
			}
			Map<Variable, Constant> model = new HashMap<>();
			for (Map.Entry<Variable, IntVar> entry : variableMap.entrySet()) {
				model.put(entry.getKey(), new IntConstant(entry.getValue().getValue()));
			}
			log.trace("model: {}", model);
			return new Model(true, model);
		} catch (TranslatorUnsupportedOperation x) {
			log.warn(x.getMessage(), x);
		} catch (VisitorException x) {
			log.fatal("encountered an exception -- this should not be happening!", x);
		}
		return null;
	}

}
