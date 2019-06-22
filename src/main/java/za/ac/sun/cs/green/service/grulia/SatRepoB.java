package za.ac.sun.cs.green.service.grulia;

import java.util.Iterator;
import java.util.TreeSet;

import za.ac.sun.cs.green.Green;

/**
 * Description: Storage unit for the possible reusable models of the satisfied
 * expressions.
 *
 * @date: 2018/08/23
 * @author: JH Taljaard (USnr 18509193)
 * @author: Willem Visser (2018) (supervisor)
 * @author: Jaco Geldenhuys (2017) (supervisor)
 */
public class SatRepoB extends BinaryRepo {

	private static final long serialVersionUID = 6087675126011461571L;

	/**
	 * Contains the entries in the repo.
	 */
	@SuppressWarnings("unused")
	private TreeSet<Entry> entries;
	private boolean defaultZero;

	public SatRepoB(Green solver, boolean defaultZero) {
		super(solver, defaultZero);
		this.entries = new TreeSet<>();
		this.defaultZero = defaultZero;
	}

	/**
	 * To test if the two objects are of the same size.
	 *
	 * @param a           size of new model
	 * @param desiredSize desired model size
	 * @return if a is the same size as b
	 */
	private boolean isValid(int a, int desiredSize) {
		return a >= desiredSize;
	}

	@Override
	protected Entry next(Iterator<Entry> list, int numOfVars) {
		Entry tmp;
		while (list.hasNext()) {
			tmp = list.next();
			if (defaultZero) {
				return tmp;
			} else {
				if (isValid(tmp.getSize(), numOfVars)) {
					return tmp;
				}
			}
		}
		return null;
	}
}
