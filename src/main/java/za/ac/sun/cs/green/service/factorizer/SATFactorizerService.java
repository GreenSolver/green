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
    private int factorCount = 0; // number of facotirs
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
        Set<Instance> result = (Set<Instance>) instance.getData(getClass());
        if (result == null) {
            final Set<Expression> factors = factorizer.factorize(instance.getFullExpression());
            instance.setData(FactorExpression.class, factors);

            result = new HashSet<Instance>();
            for (Expression e : factors) {
//				log.info("Factorizer computes instance for :" + e);
                final Instance i = new Instance(getSolver(), instance.getSource(), null, e);
                result.add(i);
            }

            result = Collections.unmodifiableSet(result);
            instance.setData(FACTORS, result);
            instance.setData(FACTORS_UNSOLVED, new HashSet<Instance>(result));

//			log.info("Factorizer exiting with " + result.size() + " results");
            constraintCount++;
            factorCount += factors.size();
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
        reporter.report(getClass().getSimpleName(), "invocations = " + invocationCount);
        reporter.report(getClass().getSimpleName(), "totalConstraints = " + constraintCount);
        reporter.report(getClass().getSimpleName(), "factoredConstraints = " + factorCount);
        reporter.report(getClass().getSimpleName(), "timeConsumption = " + timeConsumption);

//        reporter.report(getClass().getSimpleName(), "collectorTime = " + factorizer.collectorTime);
//        reporter.report(getClass().getSimpleName(), "connectedTime = " + factorizer.connectedTime);
//        reporter.report(getClass().getSimpleName(), "conjunctsTime = " + factorizer.conjunctsTime);
    }
}

