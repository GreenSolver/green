package za.ac.sun.cs.green.service.grulia.repository;

import java.util.ArrayList;
import java.util.Collections;
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
		return Collections.unmodifiableList(selection);
	}

}
