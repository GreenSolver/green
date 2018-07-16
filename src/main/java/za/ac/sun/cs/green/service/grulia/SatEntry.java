package za.ac.sun.cs.green.service.grulia;

import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.Variable;

import java.util.HashMap;
import java.util.Map;

/**
 * @date: 2018/06/20
 * @author: JH Taljaard.
 * Student Number: 18509193.
 * Supervisor:  Willem Visser   (2018),
 *              Jaco Geldenhuys (2017)
 *
 * Description:
 * SatEntry stored in the SatRepo.
 */
public class SatEntry extends Entry  {

    /**
     * The SAT-Delta value
     */
    private Double SATDelta;

    /**
     * The mapping of each variable to its corresponding value.
     */
    private Map<Variable, Constant> solution;

    public SatEntry(Double SATDelta, Map<Variable, Constant> solution) {
        super(SATDelta, solution);
        this.SATDelta = SATDelta;
        this.solution = solution;
    }

    public SatEntry(Double SATDelta, Map<Variable, Integer> solution, boolean dummy) {
        super(SATDelta, solution);
        this.SATDelta = SATDelta;
        this.solution = new HashMap<>();
        for (Map.Entry<Variable, Integer> e : solution.entrySet()) {
            this.solution.put(e.getKey(), new IntConstant(e.getValue()));
        }
    }

    /**
     * Getter method for the mapping of the variables.
     *
     * @return a map of the variables.
     */
    @Override
    public Map<Variable, Constant> getSolution() {
        return this.solution;
    }

    @Override
    public int getSize() {
        return solution.size();
    }
}
