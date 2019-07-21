/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
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
	 * @param satDelta
	 *                 SatDelta value for the new entry
	 * @param core
	 *                 core for the new entry
	 */
	public CoreEntry(double satDelta, Set<Expression> core) {
		super(satDelta);
		this.core = core;
	}

	/**
	 * Core entries are always valid.
	 *
	 * @param entry
	 *              ignored reference entry
	 * @return always {@code true}
	 *
	 * @see za.ac.sun.cs.green.service.grulia.Entry#isValidFor(za.ac.sun.cs.green.service.grulia.Entry)
	 */
	@Override
	public boolean isValidFor(Entry entry) {
		return true;
	}

	@Override
	public String toString0() {
		StringBuilder s = new StringBuilder();
		s.append("core=");
		Set<Expression> core = getCore();
		if (core == null) {
			s.append("null");
		} else {
			s.append(new TreeSet<>(core));
		}
		return s.toString();
	}

}
