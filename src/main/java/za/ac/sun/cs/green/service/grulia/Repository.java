package za.ac.sun.cs.green.service.grulia;

import java.util.List;

/**
 * Description: Repository interface for Grulia store.
 *
 * @date: 2018/08/23
 * @author: JH Taljaard. Student Number: 18509193
 * @author: Willem Visser (2018, 2019) (supervisor)
 * @author: Jaco Geldenhuys (2017) (supervisor)
 */
public interface Repository<E extends Entry> {

	void clear();
	
	void add(E entry);

	int size();

	List<E> getAllEntries();

	List<E> getEntries(int limit, E startingPoint);
	
}
