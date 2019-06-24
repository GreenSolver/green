package za.ac.sun.cs.green.service.factorizer;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Service;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.service.BasicService;
import za.ac.sun.cs.green.util.Reporter;

public class SATOldFactorizerService extends BasicService {

	private static final String FACTORS = "FACTORS";

	private static final String FACTORS_UNSOLVED = "FACTORS_UNSOLVED";
	
	/**
	 * Number of times the factorizer has been invoked.
	 */
	private int invocationCount = 0;

	/**
	 * Total number of constraints processed.
	 */
	private int constraintCount = 0;

	/**
	 * Number of factored constraints returned.
	 */
	private int factorCount = 0;
    private long timeConsumption = 0;

	public SATOldFactorizerService(Green solver) {
		super(solver);
	}

	@Override
	public Set<Instance> processRequest(Instance instance) {
        long startTime = System.currentTimeMillis();
        invocationCount++;
		@SuppressWarnings("unchecked")
		Set<Instance> result = (Set<Instance>) instance.getData(FACTORS);
		if (result == null) {
			final Instance p = instance.getParent();

			FactorExpressionOld fc0 = null;
			if (p != null) {
				fc0 = (FactorExpressionOld) p.getData(FactorExpressionOld.class);
				if (fc0 == null) {
					// Construct the parent's factor and store it
					fc0 = new FactorExpressionOld(null, p.getFullExpression());
					p.setData(FactorExpressionOld.class, fc0);
				}
			}

			final FactorExpressionOld fc = new FactorExpressionOld(fc0, instance.getExpression());
			instance.setData(FactorExpressionOld.class, fc);

			result = new HashSet<Instance>();
			for (Expression e : fc.getFactors()) {
//				log.info("Factorizer computes instance for :" + e);
				final Instance i = new Instance(getSolver(), instance.getSource(), null, e);
				result.add(i);
			}
			result = Collections.unmodifiableSet(result);
			instance.setData(FACTORS, result);
			instance.setData(FACTORS_UNSOLVED, new HashSet<Instance>(result));

//			log.info("Factorize exiting with " + result.size() + " results");

			constraintCount += 1;
			factorCount += fc.getNumFactors();
		}
        timeConsumption += (System.currentTimeMillis() - startTime);
        return result;
	}

	@Override
	public Object childDone(Instance instance, Service subservice, Instance subinstance, Object result) {
		Boolean issat = (Boolean) result;
		if ((issat != null) && !issat) {
			return false;
		}
		@SuppressWarnings("unchecked")
		HashSet<Instance> unsolved = (HashSet<Instance>) instance.getData(FACTORS_UNSOLVED);
		if (unsolved.contains(subinstance)) {
			// Remove the subinstance now that it is solved 
			unsolved.remove(subinstance);
			instance.setData(FACTORS_UNSOLVED, unsolved);
			// Return true if no more unsolved factors; else return null to carry on the computation
			return (unsolved.isEmpty()) ? result : null; 
		} else {
			// We have already solved this subinstance; return null to carry on the computation
			return null;
		}
	}

	@Override
	public Object allChildrenDone(Instance instance, Object result) {
		@SuppressWarnings("unchecked")
		HashSet<Instance> unsolved = (HashSet<Instance>) instance.getData(FACTORS_UNSOLVED);
		if (unsolved.size() >= 1 && result == null) {
			log.fatal("Unsolved Factors but result is null -> concurrency bug");
			result = true;
		}
		return result;
	}
	
	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("invocations", invocationCount);
		reporter.report("totalConstraints", constraintCount);
		reporter.report("factoredConstraints", factorCount);
        reporter.report("timeConsumption", timeConsumption);
	}

}
