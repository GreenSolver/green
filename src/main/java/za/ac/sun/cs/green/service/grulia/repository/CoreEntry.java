package za.ac.sun.cs.green.service.grulia.repository;

import java.util.Set;

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
	 * Construct a new model entry.
	 * 
	 * @param satDelta SatDelta value for the new entry
	 * @param model    model for the new entry
	 */
	public CoreEntry(double satDelta, Set<Expression> core) {
		super(satDelta);
		this.core = core;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * za.ac.sun.cs.green.service.grulia.repository.Entry#isValidFor(za.ac.sun.cs.
	 * green.service.grulia.repository.Entry)
	 */
	@Override
	public boolean isValidFor(Entry entry) {
		return true;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		StringBuilder s = new StringBuilder();
		s.append("(satDelta=").append(getSatDelta());
		s.append(", core=").append(getCore());
		s.append(')');
		return s.toString();
	}

}
