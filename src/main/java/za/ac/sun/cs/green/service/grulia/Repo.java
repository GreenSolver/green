package za.ac.sun.cs.green.service.grulia;

import za.ac.sun.cs.green.expr.IntVariable;
import java.util.SortedSet;

/**
 * Description: Repository interface for Grulia store.
 *
 * @date: 2018/08/23
 * @author: JH Taljaard. Student Number: 18509193
 * @author: Willem Visser (2018, 2019) (supervisor)
 * @author: Jaco Geldenhuys (2017) (supervisor)
 */
public interface Repo {

	void add(Entry entry);

	Entry[] getEntries();

	int size();

	Entry[] extract(Double satDelta, SortedSet<IntVariable> variables, int k);

	void flushAll();

	void clear();

}
