package za.ac.sun.cs.green.service.grulia;

import za.ac.sun.cs.green.expr.Expression;
import java.io.Serializable;
import java.util.Set;

/**
 * Description: UnsatEntry stored in the UnsatRepo.
 *
 * @date: 2018/08/23
 * @author: JH Taljaard (USnr 18509193)
 * @author: Willem Visser (2018) (supervisor)
 * @author: Jaco Geldenhuys (2017) (supervisor)
 */
@SuppressWarnings("serial")
public class UnsatEntry extends Entry implements Comparable<Entry>, Serializable {

	public UnsatEntry(Double satDelta, Set<Expression> solution) {
		super(satDelta, solution);
	}

	/**
	 * Get the unsat core
	 * 
	 * @return expression of unsat-core
	 */
	@SuppressWarnings("unchecked")
	@Override
	public Set<Expression> getSolution() {
		return (Set<Expression>) this.solution;
	}

	/**
	 * Unable to calculate number of variables.
	 * 
	 * @return specific garbage value
	 */
	@Override
	public int getSize() {
		return -1;
	}

}
