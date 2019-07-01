package za.ac.sun.cs.green.service.grulia;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class LinearRepository<E extends Entry> implements Repository<E> {

	/**
	 * List of entries.
	 */
	protected final List<E> entries = new ArrayList<>();

	@Override
	public void clear() {
		entries.clear();
	}

	@Override
	public void add(E entry) {
		int size = size();
		double target = entry.getSatDelta();
		int lo = 0, hi = size - 1, mid = (lo + hi) >>> 1;
		while (lo < hi) {
			double value = entries.get(mid).getSatDelta();
			if (value < target) {
				lo = mid + 1;
			} else if (value > target) {
				hi = mid - 1;
			} else {
				break;
			}
			mid = (lo + hi) >>> 1;
		}
		entries.add(mid, entry);
	}

	@Override
	public int size() {
		return entries.size();
	}

	@Override
	public List<E> getAllEntries() {
		return Collections.unmodifiableList(entries);
	}

	@Override
	public List<E> getEntries(int limit, E startingPoint) {
		List<E> selection = new ArrayList<>(limit);
		int selected = 0;
		// First we find the closest entry with binary search on SatDelta
		int size = size();
		double target = startingPoint.getSatDelta();
		int lo = 0, hi = size - 1, mid = (lo + hi) >>> 1;
		while (lo < hi) {
			double value = entries.get(mid).getSatDelta();
			if (value < target) {
				lo = mid + 1;
			} else if (value > target) {
				hi = mid - 1;
			} else {
				break;
			}
			mid = (lo + hi) >>> 1;
		}
		// Now add closest entries, working leftwards and rightwards
		int indexL = mid, indexR = mid - 1;
		E entryL = null, entryR = null;
		double satDeltaL = 0.0, satDeltaR = 0.0;
		while (selected < limit) {
			// Find the next LEFT entry if necessary
			if (entryL == null) {
				while (indexL > 0) {
					E e = entries.get(--indexL);
					if (e.isValidFor(startingPoint)) {
						entryL = e; 
						satDeltaL = entryL.getSatDelta();
						break;
					}
				}
			}
			// Find the next RIGHT entry if necessary
			if (entryR == null) {
				while (indexR < size - 1) {
					E e = entries.get(++indexR);
					if (e.isValidFor(startingPoint)) {
						entryR = e;
						satDeltaR = entryR.getSatDelta();
						break;
					}
				}
			}
			if ((entryL == null) && (entryR == null)) {
				// No more available, we must stop
				break;
			} else if (entryL == null) {
				// Copy RIGHT until full or no more available
				while ((selected < limit) && (entryR != null)) {
					selection.add(entryR);
					selected++;
					entryR = null;
					while (indexR < size - 1) {
						E e = entries.get(++indexR);
						if (e.isValidFor(startingPoint)) {
							entryR = e;
							satDeltaR = entryR.getSatDelta();
							break;
						}
					}
				}
				break;
			} else if (entryR == null) {
				// Copy LEFT until full or no more available
				while ((selected < limit) && (entryL != null)) {
					selection.add(entryL);
					selected++;
					entryL = null;
					while (indexL > 0) {
						E e = entries.get(--indexL);
						if (e.isValidFor(startingPoint)) {
							entryL = e;
							satDeltaL = entryL.getSatDelta();
							break;
						}
					}
				}
				break;
			} else if (target - satDeltaL < satDeltaR - target) {
				// Copy LEFT because it is closest
				selection.add(entryL);
				selected++;
				entryL = null;
			} else {
				// Copy RIGHT because it is closest
				selection.add(entryR);
				selected++;
				entryR = null;
			}
		}
		return Collections.unmodifiableList(selection);
	}

}
