package za.ac.sun.cs.green.service.grulia;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.PriorityQueue;

/**
 * Description: Storage unit for the possible reusable unsat-cores of the
 * unsatisfied expressions.
 *
 * @date: 2018/08/23
 * @author: JH Taljaard (USnr 18509193)
 * @author: Willem Visser (2018) (supervisor)
 * @author: Jaco Geldenhuys (2017) (supervisor)
 */
public class UnsatRepoA extends LinearRepo {

	/**
	 * Contains the entries in the repo.
	 */
	private List<Entry> entries;
	private HashMap<Double, String> unsatHashcache;

	public UnsatRepoA(boolean defaultZero) {
		super(false);
		this.entries = new ArrayList<Entry>();
		this.unsatHashcache = new HashMap<>();
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
			this.unsatHashcache.put(entry.getSATDelta(), entry.getSolution().toString());
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
		unsatHashcache.clear();
	}

	@Override
	protected Entry[] allEntries(Double satDelta, int n) {
		this.entries.sort(new CompareToReferenceScore(0.0));
		Entry[] entriesCopy = new Entry[this.size()];
		int i = 0;
		for (Entry e : this.entries) {
			entriesCopy[i++] = e;
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
