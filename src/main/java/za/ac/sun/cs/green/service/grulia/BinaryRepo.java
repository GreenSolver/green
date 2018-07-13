package za.ac.sun.cs.green.service.grulia;

import za.ac.sun.cs.green.expr.IntVariable;

import java.io.Serializable;
import java.util.*;

/**
 * @date: 2018/06/20
 * @author: JH Taljaard.
 * Student Number: 18509193.
 * Supervisor:  Willem Visser   (2018),
 *              Jaco Geldenhuys (2017)
 *
 * Description:
 * Parent for cache implementing RB-Tree.
 */
public abstract class BinaryRepo implements Repo, Comparator<Entry>, Serializable {

    /**
     * Contains the entries in the repo.
     */
    private TreeSet<Entry> entries;
    private boolean default_zero;

    public BinaryRepo(boolean default_zero) {
        this.entries = new TreeSet<>();
        this.default_zero = default_zero;
    }

    @Override
    public int compare(Entry e1, Entry e2) {
        double referenceScore = 0.0;
        Double e1Delta = Math.abs(referenceScore - (e1.getSATDelta()));
        Double e2Delta = Math.abs(referenceScore - (e2.getSATDelta()));
        return e1Delta.compareTo(e2Delta);
    }

    /**
     * To add an entry to the repo.
     *
     * @param entry the entry to be added.
     */
    public void add(Entry entry) {
        this.entries.add(entry);
    }

    public Entry[] getEntries() {
        return (Entry[]) entries.toArray();
    }

    /**
     * @return the number of entries in the repo.
     */
    public int size() {
        return this.entries.size();
    }

    protected abstract Entry next(Iterator<Entry> list, int numOfVars);

    private Entry[] allEntries(int numOfVars) {
        int n = this.size();
        Entry[] entriesCopy = new Entry[n];
        Iterator<Entry> entries = this.entries.iterator();
        Entry temp = null;
        for (int i = 0; i < n; i++) {
            temp = next(entries, numOfVars);
            if (temp != null) {
                entriesCopy[i] = temp;
            } else {
                break;
            }
        }
        return entriesCopy;
    }

    private Entry[] binarySearch(Double sd, int k, int numOfVars) {
        SatEntry dummy = new SatEntry(sd, null);
        NavigableSet<Entry> head = entries.headSet(dummy,true);
        NavigableSet<Entry> tail = entries.tailSet(dummy, false);

        Iterator<Entry> upper = tail.iterator();
        Iterator<Entry> lower = head.descendingSet().iterator();

        Entry l = next(lower, numOfVars);
        Entry u = next(upper, numOfVars);

        double deltaU, deltaL;
        Entry[] closests = new Entry[k];

        for (int i = 0; i < k; i++) {

            if (u != null) {
                deltaU = u.getSATDelta() - sd;
            } else {
                deltaU = Double.MAX_VALUE;
            }

            if (l != null) {
                deltaL = sd - l.getSATDelta();
            } else {
                deltaL = Double.MAX_VALUE;
            }

            if (deltaL < deltaU) {
                closests[i] = l;
                l = next(lower, numOfVars);
            } else {
                closests[i] = u;
                u = next(upper, numOfVars);
            }
        }

        return closests;
    }

    /**
     * Returns k entries closest to the given SATDelta.
     *
     * @param SATDelta the given SATDelta to use as reference for filtering
     * @param variables a given list of variables used in the expression
     * @param k the number of entries to extract
     * @return the filtered entries, sorted by increasing distance from the given SATDelta.
     */
    private Entry[] filterByProximity(Double SATDelta, SortedSet<IntVariable> variables, int k) {
        int numOfVars = variables.size();
        if (this.size() <= k) {
            // If the number of requested entries exceeds the available entries,
            // return them all in the right order.
            return allEntries(numOfVars);
        }

        return binarySearch(SATDelta, k, numOfVars);
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
