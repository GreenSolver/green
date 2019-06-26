package za.ac.sun.cs.green.service.grulia.repository;

import java.util.Map;

import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.Variable;

/**
 * Entry for models.
 */
public class ModelEntry extends Entry {

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
		this.modelSize = model.size();
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

//	/* (non-Javadoc)
//	 * @see za.ac.sun.cs.green.service.grulia.repository.Entry#compareTo0(za.ac.sun.cs.green.service.grulia.repository.Entry)
//	 */
//	@Override
//	public int compareTo0(Entry entry) {
//		// IS THIS CORRECT?  SHOULD WE IGNORE MODELS?
//		return 0;
//	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * za.ac.sun.cs.green.service.grulia.repository.Entry#isValidFor(za.ac.sun.cs.
	 * green.service.grulia.repository.Entry)
	 */
	@Override
	public boolean isValidFor(Entry entry) {
		return getModelSize() >= ((ModelEntry) entry).getModelSize();
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
		s.append(", model=").append(getModel());
		s.append(", size=").append(getModelSize());
		s.append(')');
		return s.toString();
	}

}
