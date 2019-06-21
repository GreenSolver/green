package za.ac.sun.cs.green.service.factorizer;

import org.apache.logging.log4j.status.StatusLogger;
import za.ac.sun.cs.green.expr.*;
import java.util.*;
import org.apache.logging.log4j.Logger;

/**
 * Helper class to factorize an expression.
 */
public class FactorExpression {
    private Set<Expression> factors = null;
    private Collector collector = null;
    private UnionFind<Expression> uf = null;
    private Expression processedExpression = null;
    private int conjunctCount = 0;
    protected final Logger log;
    // stat variables
    public long collectorTime = 0;
    public long conjunctsTime = 0;
    public long connectedTime = 0;

    public long creationTime = 0;
    public long unionTime = 0;

    private int dependentConjunctCount = 0;

    public FactorExpression() {
        this.log = StatusLogger.getLogger();
    }

    public FactorExpression(final Logger log) {
        this.log = log;
    }

    public FactorExpression(Expression e) {
        this.log = StatusLogger.getLogger();
        factorize(e);
    }

    /**
     * Factorize a given expression.
     * @param full - the full expression
     * @return the set of factors of the expression
     */
    public Set<Expression> factorize(Expression full) {
        factors = new HashSet<>();
        uf = new UnionFind<>(factors);
        collector = new Collector(uf);
        processedExpression = full;

        if (full != null) {
            try {
                long start = System.currentTimeMillis();
                collector.explore(full);
                collectorTime += (System.currentTimeMillis() - start);
            } catch (VisitorException x) {
                log.fatal("encountered an exception -- this should not be happening!", x);
            }
        }

        if (uf.size() == 0) {
            factors.add(full);
            return factors;
        }

        long start = System.currentTimeMillis();
        factors = extractFactors(uf);
        conjunctsTime += (System.currentTimeMillis() - start);

        return factors;
    }

    /**
     * Builds the new dependents conjuncts (from the connected components from the tree).
     * @param uf -- UnionFind object
     * @return returns a set the new factors
     */
    private Set<Expression> extractFactors(UnionFind<Expression> uf) {
        long start = System.currentTimeMillis();
        Map<Expression, Set<Expression>> components = getConnectedComponents(uf);
        connectedTime += (System.currentTimeMillis() - start);

        Set<Expression> factors = new HashSet<>();
        for (Expression e : components.keySet()) {
            Set<Expression> conjuncts = components.get(e);
            Expression factor = null;
            conjunctCount += conjuncts.size();
            for (Expression x : conjuncts) {
                if (factor == null) {
                    factor = x;
                } else {
                    factor = new Operation(Operation.Operator.AND, factor, x);
                }
            }
            factors.add(factor);
        }
        return factors;
    }

    /**
     * Extracts the connected components from the tree.
     * @param uf -- UnionFind object
     * @return the Map of connected components
     */
    private Map<Expression, Set<Expression>> getConnectedComponents(UnionFind<Expression> uf) {
        // TODO :: Optimize
        Map<Expression, Set<Expression>> components = new LinkedHashMap<>();
        for (Expression t : uf.getParentMap().keySet()) {
            Expression representative = uf.find(t);
            if (!components.containsKey(representative)) {
                components.put(representative, new LinkedHashSet<>());
            }
            components.get(representative).add(t);
        }
        return components;
    }

    public Set<Expression> getFactors() {
        return factors;
    }

    public int getNumFactors() {
        return factors.size();
    }

    public int getVariableCount() {
        return collector.getVarCount();
    }

    public int getDependentConjunctCount() {
        return dependentConjunctCount;
    }

    public Expression getProcessedExpression() {
        return processedExpression;
    }

    public Set<Expression> getDependentFactor(Expression target) {
        // TODO :: fix for, eg target == v1&&v2 or target == fullExpression().
        // This is extra subroutine, not needed for main calculation.
        // Only added since FactorExpressionOld has it.
        // If you really want this functionality, rather use FactorExpressionOld at the moment.

        Map<Expression, Set<Expression>> components = getConnectedComponents(uf);
        Expression parent = null;
        for (Expression key : components.keySet()) {
            if (parent != null) {
                break;
            }
            if (key.toString().contains(target.toString())) {
                parent = key;
                break;
            } else if (components.get(key).toString().contains(target.toString())) {
                for (Expression clause : components.get(key)) {
                    if (clause.toString().contains(target.toString())) {
                        parent = key;
                        break;
                    }
                }
            }
        }

        Set<Expression> factors = new HashSet<>();

        if (parent == null) {
            log.info("no dependent factor");
            return null;
        }
        dependentConjunctCount = 0;
        Set<Expression> clauses = components.get(parent);
        Expression factor = null;
        for (Expression x : clauses) {
            dependentConjunctCount++;
            conjunctCount++;
            if (factor == null) {
                factor = x;
            } else {
                factor = new Operation(Operation.Operator.AND, factor, x);
            }
        }
        factors.add(factor);
        return factors;
    }

    public int getConjunctCount() {
        return conjunctCount;
    }

    private class Collector extends Visitor {
        /**
         * Stores the parent (of components of UF) with corresponding variable as index.
         */
        private Map<Variable, Expression> parents = null;

        /**
         * Tree to capture the dependent expressions.
         */
        private UnionFind<Expression> uf = null;

        /**
         * The currentConjunct being visited.
         */
        private Expression currentConjunct = null;

        private int varCount = 0;

        public int getVarCount() {
            return varCount;
        }

        public Collector(UnionFind<Expression> uf) {
            this.uf = uf;
            this.parents = new HashMap<>();
        }

        /**
         * Explores the expression by setting the default conjunct and then
         * visiting the expression.
         *
         * @param expression
         *            the expression to explore
         * @throws VisitorException
         *             should never happen
         */
        public void explore(Expression expression) throws VisitorException {
            currentConjunct = expression;
            expression.accept(this);
        }

        /*
         * (non-Javadoc)
         *
         * @see
         * za.ac.sun.cs.solver.expr.Visitor#postVisit(za.ac.sun.cs.solver.expr
         * .Variable)
         */
        @Override
        public void postVisit(Variable variable) {
            if (currentConjunct != null) {
                if (!parents.containsKey(variable)) {
                    parents.put(variable, currentConjunct);
                }

                if (!uf.getParentMap().containsKey(currentConjunct)) {
                    uf.addElement(currentConjunct);
                    uf.union(parents.get(variable), currentConjunct);
                    varCount++;
                } else {
                    uf.union(parents.get(variable), currentConjunct);
                }
            }
        }

        private boolean isOr(Expression e) {
            if (e instanceof Operation) {
                Operation.Operator op = ((Operation) e).getOperator();
                return (op == Operation.Operator.OR);
            }
            return false;
        }

        /*
         * (non-Javadoc)
         *
         * @see
         * za.ac.sun.cs.solver.expr.Visitor#preVisit(za.ac.sun.cs.solver.expr
         * .Expression)
         */
        @Override
        public void preVisit(Expression expression) {
            if (expression instanceof Operation) {
                Operation.Operator op = ((Operation) expression).getOperator();
                if (op == Operation.Operator.OR && !isOr(currentConjunct)) {
                    currentConjunct = expression;
                } else if ((op == Operation.Operator.NOT)
                        || (op == Operation.Operator.EQ)
                        || (op == Operation.Operator.NE)
                        || (op == Operation.Operator.LT)
                        || (op == Operation.Operator.LE)
                        || (op == Operation.Operator.GT)
                        || (op == Operation.Operator.GE)) {
                    currentConjunct = expression;
                }
            }
        }
    }
}
