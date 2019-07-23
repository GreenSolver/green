/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.grulia;

import java.io.Serializable;
import java.util.Map;
import java.util.TreeMap;

import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.Variable;

/**
 * Entry for models.
 */
public class ModelEntry extends Entry implements Serializable {

	/**
	 * Generated id for serialization.
	 */
	private static final long serialVersionUID = -4236947173041586106L;

	/**
	 * The model stored in this entry.
	 */
	private final Map<Variable, Constant> model;

	/**
	 * Construct a new model entry.
	 *
	 * @param satDelta
	 *                 SatDelta value for the new entry
	 * @param model
	 *                 model for the new entry
	 */
	public ModelEntry(double satDelta, Map<Variable, Constant> model) {
		super(satDelta, model.size());
		this.model = model;
	}

	/**
	 * Construct a new model entry. This version is used mostly for {@code null}
	 * models that are used as anchor points when searching for nearby models.
	 *
	 * @param satDelta
	 *                 SatDelta value for the new entry
	 * @param model
	 *                 model for the new entry
	 * @param size
	 *                 size of the model
	 */
	public ModelEntry(Double satDelta, Map<Variable, Constant> model, int size) {
		super(satDelta, size);
		this.model = model;
	}

	/**
	 * Return the model for this entry.
	 *
	 * @return the entry's model
	 */
	public Map<Variable, Constant> getModel() {
		return model;
	}

	/**
	 * Filter out models that are small than a given entry.
	 *
	 * @param entry
	 *              entry to compare to
	 * @return {@code true} if and only if this entry is larger (has more variables)
	 *         than the given entry
	 *
	 * @see za.ac.sun.cs.green.service.grulia.Entry#isValidFor(za.ac.sun.cs.green.service.grulia.Entry)
	 */
	@Override
	public boolean isValidFor(Entry entry) {
		return getSize() >= ((ModelEntry) entry).getSize();
	}

	@Override
	public String toString0() {
		StringBuilder s = new StringBuilder();
		s.append("model=");
		Map<Variable, Constant> model = getModel();
		if (model == null) {
			s.append("null");
		} else {
			s.append(new TreeMap<>(model));
		}
		return s.toString();
	}

}
