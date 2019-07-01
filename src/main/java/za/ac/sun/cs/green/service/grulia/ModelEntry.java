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
	 * The model stored in this entry.
	 */
	private final Map<Variable, Constant> model;

	/**
	 * The size of the model stored in this entry.
	 */
	private final int modelSize;

	/**
	 * Construct a new model entry.
	 *
	 * @param satDelta SatDelta value for the new entry
	 * @param model    model for the new entry
	 */
	public ModelEntry(double satDelta, Map<Variable, Constant> model) {
		super(satDelta);
		this.model = model;
		this.modelSize = model.size();
	}

	/**
	 * Construct a new model entry. This version is used mostly for {@code null}
	 * models that are used as anchor points when searching for nearby models.
	 *
	 * @param satDelta SatDelta value for the new entry
	 * @param model    model for the new entry
	 * @param size     size of the model
	 */
	public ModelEntry(Double satDelta, Map<Variable, Constant> model, int size) {
		super(satDelta);
		this.model = model;
		this.modelSize = size;
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
	 * Return the model size for this entry.
	 *
	 * @return the entry's model size
	 */
	public int getModelSize() {
		return modelSize;
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see za.ac.sun.cs.green.service.grulia.Entry#isValidFor(za.ac.sun.cs.green.service.grulia.Entry)
	 */
	@Override
	public boolean isValidFor(Entry entry) {
		return getModelSize() >= ((ModelEntry) entry).getModelSize();
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see java.lang.Object#toString0()
	 */
	@Override
	public String toString0() {
		StringBuilder s = new StringBuilder();
		s.append("model=").append(new TreeMap<>(getModel()));
		s.append(", size=").append(getModelSize());
		return s.toString();
	}

}
