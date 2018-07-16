package za.ac.sun.cs.green.service.grulia;

import za.ac.sun.cs.green.expr.IntVariable;
import java.util.SortedSet;

/**
 * @date: 2017/06/23
 * @author: JH Taljaard.
 * Student Number: 18509193.
 * Supervisor:  Willem Visser   (2018),
 *              Jaco Geldenhuys (2017)
 *
 * Description:
 * Repository interface for caches.
 */
public interface Repo {

    public void add(Entry entry);

    public Entry[] getEntries();

    public int size();

    public Entry[] extract(Double SATDelta, SortedSet<IntVariable> variables, int k);

}
