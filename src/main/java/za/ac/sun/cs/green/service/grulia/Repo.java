package za.ac.sun.cs.green.service.grulia;

import za.ac.sun.cs.green.expr.IntVariable;
import java.util.SortedSet;

/**
 * @date: 2018/08/23
 * @author: JH Taljaard.
 * Student Number: 18509193.
 * Supervisor:  Willem Visser   (2018,2019),
 *              Jaco Geldenhuys (2017)
 *
 * Description:
 * Repository interface for Grulia store.
 */
public interface Repo {

    public void add(Entry entry);

    public Entry[] getEntries();

    public int size();

    public Entry[] extract(Double SATDelta, SortedSet<IntVariable> variables, int k);

    public void flushAll();

    public void clear();

}
