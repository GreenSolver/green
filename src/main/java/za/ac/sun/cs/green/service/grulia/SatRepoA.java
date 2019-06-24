package za.ac.sun.cs.green.service.grulia;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.PriorityQueue;

import za.ac.sun.cs.green.util.Pair;

/**
 * Description: Storage unit for the possible reusable models of the satisfied
 * expressions.
 *
 * @date: 2018/08/23
 * @author: JH Taljaard (USnr 18509193)
 * @author: Willem Visser (2018) (supervisor)
 * @author: Jaco Geldenhuys (2017) (supervisor)
 */
public class SatRepoA extends LinearRepo {
	/**
	 * Contains the entries in the repo.
	 */
	private ArrayList<Entry> entries;
	private HashMap<Double, String> satHashcache;
	private boolean defaultZero;

	public SatRepoA(boolean defaultZero) {
		super(defaultZero);
		this.entries = new ArrayList<Entry>();
		this.satHashcache = new HashMap<>();
		this.defaultZero = defaultZero;
	}

	/**
	 * To add an entry to the repo.
	 *
	 * @param entry the entry to be added.
	 */
	@Override
	public void add(Entry entry) {
		if (!this.contains(entry)) {
			this.entries.add(entry);
			this.satHashcache.put(entry.getSATDelta(), entry.getSolution().toString());
		}
	}

	@Override
	public int size() {
		return this.entries.size();
	}

	@Override
	public void flushAll() {

	}

	@Override
	public void clear() {
		entries.clear();
		satHashcache.clear();
	}

	/**
	 * To test if the two objects are of the same size.
	 *
	 * @param a           size of new model
	 * @param desiredSize desired model size
	 * @return if a is the same size as b
	 */
	private boolean isValid(int a, int desiredSize) {
		return a >= desiredSize;
	}

	@Override
	protected Entry[] allEntries(Double satDelta, int n) {
		Entry[] entriesCopy = new Entry[this.size()];
		this.entries.sort(new CompareToReferenceScore(0.0));
		int i = 0;
		for (Entry e : this.entries) {
			if (isValid(e.getSize(), n)) {
				entriesCopy[i] = e;
				i++;
			}
		}
		return entriesCopy;
	}

	@Override
	protected Entry[] linearSearch(Double satDelta, int n, int k) {
		PriorityQueue<Pair<Double, Entry>> queue = new PriorityQueue<>(k,
				(p1, p2) -> ((-1) * (p1.getL().compareTo(p2.getL()))));

		// Load the first k entries in the queue, then keep updating the queue
		// inserting elements whose distance from satDelta is smaller than the
		// distance of the maximum element in the queue. The maximum is removed
		// whenever a new elements is inserted so that the overall complexity
		// of this method is O(n*log(k)).
		int i = 0;
		for (final Entry entry : this.entries) {
			if (!defaultZero) {
				if (!isValid(entry.getSize(), n)) {
					// Entries containing models with less variables than
					// the reference expression are immediately discarded.
					continue;
				}
			}
			Double delta = Math.abs(entry.getSATDelta() - satDelta);

			if (i++ < k) {
				queue.add(new Pair<>(delta, entry));
			} else {
				Pair<Double, Entry> head = queue.peek();
				if (delta.compareTo(head.getL()) < 0) {
					queue.poll();
					queue.add(new Pair<>(delta, entry));
				}
			}
		}

		Entry[] closest = new Entry[k];
		int j = k - 1;
		while (!queue.isEmpty()) {
			closest[j] = queue.remove().getR();
			j--;
		}

		return closest;
	}
}
