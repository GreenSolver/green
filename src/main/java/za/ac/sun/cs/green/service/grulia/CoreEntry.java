package za.ac.sun.cs.green.service.grulia;

import java.util.Set;
import java.util.TreeSet;

import za.ac.sun.cs.green.expr.Expression;

/**
 * Entry for unsatisfying cores.
 */
public class CoreEntry extends Entry {

	/**
	 * The core stored in this entry.
	 */
	private final Set<Expression> core;

	/**
	 * Return the core for this entry.
	 *
	 * @return the entry's core
	 */
	public Set<Expression> getCore() {
		return core;
	}

	/**
	 * Construct a new core entry.
	 *
	 * @param satDelta SatDelta value for the new entry
	 * @param core     core for the new entry
	 */
	public CoreEntry(double satDelta, Set<Expression> core) {
		super(satDelta);
		this.core = core;
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see za.ac.sun.cs.green.service.grulia.Entry#isValidFor(za.ac.sun.cs.green.service.grulia.Entry)
	 */
	@Override
	public boolean isValidFor(Entry entry) {
		return true;
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see java.lang.Object#toString0()
	 */
	@Override
	public String toString0() {
		StringBuilder s = new StringBuilder();
		s.append("model=").append(new TreeSet<>(getCore()));
		return s.toString();
	}

}
