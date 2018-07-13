package za.ac.sun.cs.green.service.grulia;

import java.io.Serializable;

/**
 * @date: 2018/06/20
 * @author: JH Taljaard.
 * Student Number: 18509193.
 * Supervisor:  Willem Visser   (2018),
 *              Jaco Geldenhuys (2017)
 *
 * Description:
 * Parent class for Entry stored in the Repo.
 */
public abstract class Entry implements Comparable<Entry>, Serializable {

    /**
     * The SAT-Delta value
     */
    private Double SATDelta;

    /**
     * The solution can be a map of the models or expression of the unsat-core
     */
    private Object solution;

    public Entry(Double SATDelta, Object solution) {
        this.SATDelta = SATDelta;
        this.solution = solution;
    }

    public abstract Object getSolution();

    /**
     * Number of variables
     * @return
     */
    public abstract int getSize();

    public Double getSATDelta() {
        return SATDelta;
    }

    public int equals(Entry e1) {
        if (this.getSolution() == null || e1.getSolution() == null) {
            return 1;
        }
        return (this.hashCode() == e1.hashCode()) ? 0 : 1;
    }

    @Override
    public int compareTo(Entry e2) {
        double referenceScore = 0.0;
        Double e1Delta = Math.abs(referenceScore - this.getSATDelta());
        Double e2Delta = Math.abs(referenceScore - e2.getSATDelta());
        int comp = e1Delta.compareTo(e2Delta);
        return (comp != 0) ? comp : this.equals(e2);
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        String sequence = ((getSATDelta().toString()) + (getSolution().toString()));
        result = prime * result + sequence.hashCode();
        return result;
    }

    @Override
    public String toString() {
        return String.format(
                "Entry(SATDelta=%s, {variable, value}=%s)",
                SATDelta,
                solution.toString());
    }
}
