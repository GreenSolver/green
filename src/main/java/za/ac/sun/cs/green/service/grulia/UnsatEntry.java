package za.ac.sun.cs.green.service.grulia;

import za.ac.sun.cs.green.expr.Expression;
import java.io.Serializable;
import java.util.Set;

/**
 * @date: 2018/06/20
 * @author: JH Taljaard.
 * Student Number: 18509193.
 * Supervisor:  Willem Visser   (2018),
 *              Jaco Geldenhuys (2017)
 *
 * Description:
 * UnsatEntry stored in the UnsatRepo.
 */
public class UnsatEntry extends Entry implements Comparable<Entry>, Serializable {

    /**
     * The SAT-Delta value
     */
    private Double SATDelta;

    /**
     * The list of unsat cores.
     */
    private Set<Expression> solution;

    public UnsatEntry(Double SATDelta, Set<Expression> solution) {
        super(SATDelta, solution);
        this.SATDelta = SATDelta;
        this.solution = solution;
    }

    /**
     * Get the unsat core
     * @return expression of unsat-core
     */
    @Override
    public Set<Expression> getSolution() {
        return this.solution;
    }

    /**
     * Unable to calculate number of variables.
     * @return
     */
    @Override
    public int getSize() {
        return -1;
    }
}
