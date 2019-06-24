package za.ac.sun.cs.green.service.factorizer;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Service;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.service.BasicService;
import za.ac.sun.cs.green.util.Reporter;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

public class SATFactorizerService extends BasicService {

    private FactorExpression factorizer;
    private static final String FACTORS = "FACTORS";
    private static final String FACTORS_UNSOLVED = "FACTORS_UNSOLVED";

    private int invocationCount = 0; // number of times factorizer has been invoked
    private int constraintCount = 0; // constraints processed
    private int factorCount = 0; // number of factors
    private long timeConsumption = 0;

    public SATFactorizerService(Green solver) {
        super(solver);
        factorizer = new FactorExpression(log);
    }

    @Override
    public Set<Instance> processRequest(Instance instance) {
        long startTime = System.currentTimeMillis();
        invocationCount++;

        @SuppressWarnings("unchecked")
        Set<Instance> result = (Set<Instance>) instance.getData(FACTORS);
        if (result == null) {
//            final Instance p = instance.getParent();
//            if (p != null) {
//                factorizer = (FactorExpression) p.getData(FactorExpression.class);
//            }
//            if (factorizer != null) {
//                return null;
//            }
            final FactorExpression fc = new FactorExpression(instance.getFullExpression());
            instance.setData(FactorExpression.class, fc);
            factorizer = fc;

            result = new HashSet<Instance>();
            for (Expression e : fc.getFactors()) {
//				log.info("Factorizer computes instance for :" + e);
                final Instance i = new Instance(getSolver(), instance.getSource(), null, e);
                result.add(i);
            }

            result = Collections.unmodifiableSet(result);
            instance.setData(FACTORS, result);
            instance.setData(FACTORS_UNSOLVED, new HashSet<Instance>(result));

//			log.info("Factorizer exiting with " + result.size() + " results");
            constraintCount++;
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
        reporter.report("conjunctCount", factorizer.getConjunctCount());
        reporter.report("timeConsumption", timeConsumption);

//        reporter.reportZZ("collectorTime = " + factorizer.collectorTime);
//        reporter.reportZZ("connectedTime = " + factorizer.connectedTime);
//        reporter.reportZZ("conjunctsTime = " + factorizer.conjunctsTime);
    }
}

