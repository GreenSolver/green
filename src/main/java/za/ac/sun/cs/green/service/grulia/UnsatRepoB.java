package za.ac.sun.cs.green.service.grulia;

import java.util.*;

/**
 * @date: 2018/06/20
 * @author: JH Taljaard.
 * Student Number: 18509193.
 * Supervisor:  Willem Visser   (2018),
 *              Jaco Geldenhuys (2017)
 *
 * Description:
 * Storage unit for the possible reusable unsat-cores of the unsatisfied expressions.
 */
public class UnsatRepoB extends BinaryRepo {

    /**
     * Contains the entries in the repo.
     */
    private TreeSet<Entry> entries;

    public UnsatRepoB(boolean default_zero) {
        super(false);
        this.entries = new TreeSet<Entry>();
    }

    @Override
    protected Entry next(Iterator<Entry> list, int N) {
        if (list.hasNext()) {
            return list.next();
        } else {
            return null;
        }
    }
}
