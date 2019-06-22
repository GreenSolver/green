package za.ac.sun.cs.green.service.grulia;

import java.util.Iterator;
import java.util.TreeSet;

import za.ac.sun.cs.green.Green;

/**
 * Description: Storage unit for the possible reusable unsat-cores of the
 * unsatisfied expressions.
 *
 * @date: 2018/08/23
 * @author: JH Taljaard (USnr 18509193)
 * @author: Willem Visser (2018) (supervisor)
 * @author: Jaco Geldenhuys (2017) (supervisor)
 */
public class UnsatRepoB extends BinaryRepo {

	private static final long serialVersionUID = 5534171617262626219L;

	/**
	 * Contains the entries in the repo.
	 */
	@SuppressWarnings("unused")
	private TreeSet<Entry> entries;

	public UnsatRepoB(Green solver, boolean defaultZero) {
		super(solver, false);
		this.entries = new TreeSet<Entry>();
	}

	@Override
	protected Entry next(Iterator<Entry> list, int n) {
		if (list.hasNext()) {
			return list.next();
		} else {
			return null;
		}
	}

}
