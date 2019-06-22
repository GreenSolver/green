package za.ac.sun.cs.green.service.grulia;

import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.Variable;

import java.util.HashMap;
import java.util.Map;

/**
 * Description: SatEntry stored in the SatRepo.
 *
 * @date: 2018/06/20
 * @author: JH Taljaard (USnr 18509193)
 * @author: Willem Visser (2018) (supervisor)
 * @author: Jaco Geldenhuys (2017) (supervisor)
 */
public class SatEntry extends Entry {

	private static final long serialVersionUID = 4868061108167182194L;

	/**
	 * The mapping of each variable to its corresponding value.
	 */
	private Map<Variable, Constant> solution;

	public SatEntry(Double satDelta, Map<Variable, Constant> solution) {
		super(satDelta, solution);
	}

	public SatEntry(Double satDelta, Map<Variable, Integer> solution, boolean dummy) {
		super(satDelta, solution);
		this.solution = new HashMap<>();
		for (Map.Entry<Variable, Integer> e : solution.entrySet()) {
			this.solution.put(e.getKey(), new IntConstant(e.getValue()));
		}
	}

	/**
	 * Getter method for the mapping of the variables.
	 *
	 * @return a map of the variables.
	 */
	@Override
	public Map<Variable, Constant> getSolution() {
		return this.solution;
	}

	@Override
	public int getSize() {
		return solution.size();
	}

}
