package za.ac.sun.cs.green.service.factorizer;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Service;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.service.BasicService;
import za.ac.sun.cs.green.util.Reporter;

public class ModelFactorizerService extends BasicService {

	private static final String FACTORS = "FACTORS";
	private static final String MODELS = "MODELS";
	private static final String FACTORS_UNSOLVED = "FACTORS_UNSOLVED";

	private FactorExpression factorizer;
	private int invocationCount = 0; // number of times factorizer has been invoked
	private int constraintCount = 0; // constraints processed
	private int factorCount = 0; // number of factors
	private long timeConsumption = 0;

	public ModelFactorizerService(Green solver) {
		super(solver);
	}

	@Override
	public Set<Instance> processRequest(Instance instance) {
		long startTime = System.currentTimeMillis();
		invocationCount++;

		@SuppressWarnings("unchecked")
		Set<Instance> result = (Set<Instance>) instance.getData(FACTORS);
		if (result == null) {
//			final Instance p = instance.getParent();
//            FactorExpression fc0 = null;
//			if (p != null) {
//				fc0 = (FactorExpression) p.getData(FactorExpression.class);
//				if (fc0 == null) {
//					// Construct the parent's factor and store it
//					fc0 = new FactorExpression(p.getFullExpression());
//					p.setData(FactorExpression.class, fc0);
//				}
//			}
//			final FactorExpressionOld fc = new FactorExpressionOld(fc0, instance.getExpression());

			final FactorExpression fc = new FactorExpression(instance.getFullExpression());
			instance.setData(FACTORS, fc);
			factorizer = fc;

			result = new HashSet<Instance>();
			for (Expression e : fc.getFactors()) {
				log.debug("Factorizer computes instance for :" + e);
				final Instance i = new Instance(getSolver(), instance.getSource(), null, e);
				result.add(i);
			}
			result = Collections.unmodifiableSet(result);
			instance.setData(FACTORS, result);
			instance.setData(FACTORS_UNSOLVED, new HashSet<Instance>(result));
			instance.setData(MODELS, new HashMap<Variable, Object>());

			log.debug("Factorizer exiting with " + result.size() + " results");

			constraintCount += 1;
			factorCount += fc.getNumFactors();
		}
		timeConsumption += (System.currentTimeMillis() - startTime);
		return result;
	}

	@SuppressWarnings("unchecked")
	private boolean isUnsat(Object result) {
		if (result == null) {
			return true;
		} else if (result instanceof HashMap) {
			HashMap<Variable, Object> issat = (HashMap<Variable, Object>) result;
			return issat.isEmpty();
		} else if (result instanceof Boolean) {
			Boolean issat = (Boolean) result;
			return !issat;
		}
		return false;
	}

	@SuppressWarnings("unchecked")
	@Override
	public Object childDone(Instance instance, Service subservice, Instance subinstance, Object result) {
		HashSet<Instance> unsolved = (HashSet<Instance>) instance.getData(FACTORS_UNSOLVED);
		if (isUnsat(result)) {
			return null;
		}

		if (unsolved.contains(subinstance)) {
			// new child finished
			HashMap<Variable, Object> parentSolutions = (HashMap<Variable, Object>) instance.getData(MODELS);
			parentSolutions.putAll((HashMap<Variable, Object>) result);
			instance.setData(MODELS, parentSolutions);
			// Remove the subinstance now that it is solved
			unsolved.remove(subinstance);
			instance.setData(FACTORS_UNSOLVED, unsolved);
			// Return true of no more unsolved factors; else return null to carry on the
			// computation
			return (unsolved.isEmpty()) ? parentSolutions : null;
		} else {
			// We have already solved this subinstance; return null to carry on the
			// computation
			return null;
		}
	}

	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("invocations", invocationCount);
		reporter.report("totalConstraints", constraintCount);
		reporter.report("factoredConstraints", factorCount);
		reporter.report("conjunctCount", factorizer.getConjunctCount());
		reporter.report("timeConsumption", timeConsumption);
	}

}
