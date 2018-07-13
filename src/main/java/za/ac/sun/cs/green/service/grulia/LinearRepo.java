package za.ac.sun.cs.green.service.grulia;

import za.ac.sun.cs.green.expr.IntVariable;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.SortedSet;

/**
 * @date: 2018/06/20
 * @author: JH Taljaard.
 * Student Number: 18509193.
 * Supervisor:  Willem Visser   (2018),
 *              Jaco Geldenhuys (2017)
 *
 * Description:
 * Parent for cache implementing ArrayList with PQ building.
 */
public abstract class LinearRepo implements Repo {
    /**
     * Contains the entries in the repo.
     */
    private ArrayList<Entry> entries;
    private HashMap<Double, String> hashcache;
    private boolean default_zero;

    public LinearRepo(boolean default_zero) {
        this.entries = new ArrayList<Entry>();
        this.hashcache = new HashMap<>();
        this.default_zero = default_zero;
    }

    public abstract void add(Entry entry);

    /**
     * To check if model is already in cache.
     * @param entry entry containing model to check for
     * @return if model is in the repo
     */
    public boolean contains(Entry entry) {
        if (this.hashcache.containsKey(entry.getSATDelta())) {
            return false;
        } else if (this.hashcache.get(entry.getSATDelta()) == null) {
            return false;
        }
        return this.hashcache.get(entry.getSATDelta()).equals(entry.getSolution().toString());
    }

    public Entry[] getEntries() {
        return (Entry[]) entries.toArray();
    }

    /**
     * @return the number of entries in the repo.
     */
    public abstract int size();

    protected abstract Entry[] allEntries(Double SATDelta, int N);

    protected abstract Entry[] linearSearch(Double SATDelta, int N, int k);

    class CompareToReferenceScore implements Comparator<Entry> {
        private final Double referenceScore;

        public CompareToReferenceScore(Double referenceScore) {
            this.referenceScore = referenceScore;
        }

        @Override
        public int compare(Entry e1, Entry e2) {
            Double e1Delta = Math.abs(referenceScore - (e1.getSATDelta()));
            Double e2Delta = Math.abs(referenceScore - (e2.getSATDelta()));
            return e1Delta.compareTo(e2Delta);
        }
    }

    /**
     * Returns k entries closest to the given SATDelta.
     *
     * @author Andrea Aquino
     * @param SATDelta the given SATDelta to use as reference for filtering
     * @param variables a given list of variables used in the expression
     * @param k the number of entries to extract
     * @return the filtered entries, sorted by increasing distance from the given SATDelta.
     */
    private Entry[] filterByProximity(Double SATDelta, SortedSet<IntVariable> variables, int k) {
        int N = variables.size();
        if (this.size() <= k) {
            // If the number of requested entries exceeds the available entries,
            // return them all in the right order.
            return allEntries(SATDelta, N);
        } else {
            return linearSearch(SATDelta, N, k);
        }
    }

    /**
     * Returns k entries closest to the given SATDelta.
     *
     * @param SATDelta the given SATDelta to use as reference for filtering
     * @param variables a given list of variables used in the expression
     * @param k the number of entries to extract
     * @return the extracted entries, sorted by increasing distance from the given SATDelta.
     */
    public Entry[] extract(Double SATDelta, SortedSet<IntVariable> variables, int k) {
        if (k <= 0) {
            return new Entry[1];
        } else {
            return this.filterByProximity(SATDelta, variables, k);
        }
    }
}
