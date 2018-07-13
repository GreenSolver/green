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
 * Storage unit for the possible reusable models of the satisfied expressions.
 */
public class SatRepoB extends BinaryRepo {

    /**
     * Contains the entries in the repo.
     */
    private TreeSet<Entry> entries;
    private boolean default_zero;

    public SatRepoB(boolean default_zero) {
        super(default_zero);
        this.entries = new TreeSet<>();
        this.default_zero = default_zero;
    }

    /**
     * To test if the two objects are of the same size.
     *
     * @param a size of new model
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
            if (default_zero) {
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
