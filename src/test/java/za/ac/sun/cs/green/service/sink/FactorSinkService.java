package za.ac.sun.cs.green.service.sink;

import java.util.HashSet;
import java.util.Set;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.service.BasicService;

public class FactorSinkService extends BasicService {

	public FactorSinkService(Green solver) {
		super(solver);
	}

	@Override
	public Set<Instance> processRequest(Instance instance) {
		Instance original = instance.getSource();
		@SuppressWarnings("unchecked")
		Set<Expression> factors = (Set<Expression>) original.getData(getClass());
		if (factors == null) {
			factors = new HashSet<Expression>();
		}
		factors.add(instance.getFullExpression());
		original.setData(getClass(), factors);
		return null;
	}

}
