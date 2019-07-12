package za.ac.sun.cs.green.service.grulia;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.TreeSet;

public class BinaryRepository<E extends Entry> implements Repository<E> {

	/**
	 * List of entries.
	 */
	protected final TreeSet<E> entries = new TreeSet<>();

	@Override
	public void clear() {
		entries.clear();
	}

	@Override
	public void add(E entry) {
		entries.add(entry);
	}

	@Override
	public int size() {
		return entries.size();
	}

	@Override
	public List<E> getAllEntries() {
		return Collections.unmodifiableList(new ArrayList<>(entries));
	}

	@Override
	public List<E> getEntries(int limit, E startingPoint) {
		List<E> selection = new ArrayList<>(limit);
		int selected = 0;
		double target = startingPoint.getSatDelta();
		Iterator<E> iterL = entries.headSet(startingPoint, true).descendingIterator();
		Iterator<E> iterR = entries.tailSet(startingPoint, false).iterator();
		E entryL = null, entryR = null;
		double satDeltaL = 0.0, satDeltaR = 0.0;
		while (selected < limit) {
			// Find the next LEFT entry if necessary
			if (entryR == null) {
				while (iterL.hasNext()) {
					E e = iterL.next();
					if (e.isValidFor(startingPoint)) {
						entryL = e;
						satDeltaL = entryL.getSatDelta();
						break;
					}
				}
			}
			// Find the next RIGHT entry if necessary
			if (entryR == null) {
				while (iterR.hasNext()) {
					E e = iterR.next();
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
					while (iterR.hasNext()) {
						E e = iterR.next();
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
					while (iterL.hasNext()) {
						E e = iterL.next();
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
