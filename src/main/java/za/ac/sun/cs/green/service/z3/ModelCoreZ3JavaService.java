package za.ac.sun.cs.green.service.z3;

import java.util.*;

import com.microsoft.z3.*;
import org.apache.logging.log4j.Level;

import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.*;
import za.ac.sun.cs.green.service.ModelCoreService;
import za.ac.sun.cs.green.util.Reporter;

public class ModelCoreZ3JavaService extends ModelCoreService {

    Context ctx;
    Solver Z3solver;
    protected long timeConsumption = 0;
    protected long translationTimeConsumption = 0;
    protected long satTimeConsumption = 0;
    protected long unsatTimeConsumption = 0;
    protected int conjunctCount = 0;
    protected int variableCount = 0;
    private final static String LOGIC = "QF_LIA";

    private static class Z3Wrapper {
        private Context ctx;
        private Solver solver;

        private static Z3Wrapper instance = null;

        public static Z3Wrapper getInstance() {
            if (instance != null) {
                return instance;
            }
            return instance = new Z3Wrapper();
        }

        private Z3Wrapper() {
            HashMap<String, String> cfg = new HashMap<String, String>();
            cfg.put("model", "true");
            cfg.put("unsat_core", "true");
            cfg.put("auto_config", "false");

            try{
                ctx = new Context(cfg);
            } catch (Exception e) {
                e.printStackTrace();
                throw new RuntimeException("## Error Z3: Exception caught in Z3 JNI: \n" + e);
            }
            // TODO : Changed logic to QF_LIA from AUF_LIA
//            solver = ctx.mkSolver(LOGIC); // removed since this creation is unnecessary
        }

        public Solver getSolver() {
            return this.solver;
        }

        public Context getCtx() {
            return this.ctx;
        }
    }

    public ModelCoreZ3JavaService(Green solver, Properties properties) {
        super(solver);
        Z3Wrapper z3Wrapper = Z3Wrapper.getInstance();
        Z3solver = z3Wrapper.getSolver();
        ctx = z3Wrapper.getCtx();
    }

    @Override
    protected ModelCore modelCore(Instance instance) {
        long startTime = System.currentTimeMillis();
        ModelCore mc = null;
        // translate instance to Z3
        long T0translation = System.currentTimeMillis();
        Z3JavaTranslator translator = new Z3JavaTranslator(ctx);
        try {
            instance.getExpression().accept(translator);
        } catch (VisitorException e1) {
            log.log(Level.WARN, "Error in translation to Z3"+e1.getMessage());
        }
        // get context out of the translator
        Map<BoolExpr, Expression> namedAsserts = translator.getCoreMappings();
        // model should now be in ctx
        try {
            Z3solver = ctx.mkSolver(LOGIC); // create clean instance
            for (BoolExpr px : namedAsserts.keySet()) {
                // px is the Predicate name
                // assert and track each predicate/assertion
                Z3solver.assertAndTrack(translator.getAsserts().get(namedAsserts.get(px)), px);
            }
        } catch (Z3Exception e1) {
            log.log(Level.WARN, "Error in Z3"+e1.getMessage());
        }
        conjunctCount += instance.getExpression().getString().split("&&").length;
        variableCount += translator.getVariableCount();
        translationTimeConsumption += (System.currentTimeMillis() - T0translation);
        //solve
        try { // Real Stuff is still untested
            if (Status.SATISFIABLE == Z3solver.check()) {
                Map<Variable, Expr> variableMap = translator.getVariableMap();
                HashMap<Variable,Constant> greenModel = new HashMap<>();
                Model model = Z3solver.getModel();
                for(Map.Entry<Variable,Expr> entry : variableMap.entrySet()) {
                    Variable greenVar = entry.getKey();
                    Expr z3Var = entry.getValue();
                    Expr z3Val = model.evaluate(z3Var, false);
                    Constant val = null;
                    if (z3Val.isIntNum()) {
                        val = new IntConstant(Integer.parseInt(z3Val.toString()));
                    } else if (z3Val.isRatNum()) {
                        val = new RealConstant(Double.parseDouble(z3Val.toString()));
                    } else if (z3Val.isBV()) {
                        val = new IntegerConstant(Long.parseLong(z3Val.toString()), Long.SIZE);
                    } else {
                        log.log(Level.WARN, "Error unsupported type for variable " + z3Val);
                        return null;
                    }
                    greenModel.put(greenVar, val);
//					log.log(Level.INFO,"" + greenVar + " has value " + val);
                }
                mc = new ModelCore(true, greenModel, null);
                satCount++;
                satTimeConsumption += (System.currentTimeMillis() - startTime);
            } else {
//				log.log(Level.WARNING,"constraint has no model, it is infeasible");
                Set<Expression> clauses = new HashSet<>();
                for (Expr tmp : Z3solver.getUnsatCore()) {
                    if (tmp != null) {
                        Expression realClause = namedAsserts.get(tmp);
                        if (realClause != null) {
                            clauses.add(realClause);
                        }
                    }
                }
                mc = new ModelCore(false, null, clauses);
                unsatCount++;
                unsatTimeConsumption += (System.currentTimeMillis() - startTime);
            }
        } catch (Z3Exception e) {
            log.log(Level.WARN, "Error in Z3"+e.getMessage());
        }
        timeConsumption += (System.currentTimeMillis() - startTime);
        return mc;
    }

    @Override
    public void report(Reporter reporter) {
//        reporter.report(getClass().getSimpleName(), "cacheHitCount = " + cacheHitCount);
//        reporter.report(getClass().getSimpleName(), "cacheMissCount = " + cacheMissCount);
//        reporter.report(getClass().getSimpleName(), "satCacheHitCount = " + satHitCount);
//        reporter.report(getClass().getSimpleName(), "unsatCacheHitCount = " + unsatHitCount);
//        reporter.report(getClass().getSimpleName(), "satCacheMissCount = " + satMissCount);
//        reporter.report(getClass().getSimpleName(), "unsatCacheMissCount = " + unsatMissCount);
//        reporter.report(getClass().getSimpleName(), "satQueries = " + satCount);
//        reporter.report(getClass().getSimpleName(), "unsatQueries = " + unsatCount);
        reporter.report(getClass().getSimpleName(), "timeConsumption = " + timeConsumption);
        reporter.report(getClass().getSimpleName(), "satTimeConsumption = " + satTimeConsumption);
        reporter.report(getClass().getSimpleName(), "unsatTimeConsumption = " + unsatTimeConsumption);
        reporter.report(getClass().getSimpleName(), "translationTimeConsumption = " + translationTimeConsumption);
        reporter.report(getClass().getSimpleName(), "conjunctCount = " + conjunctCount);
        reporter.report(getClass().getSimpleName(), "variableCount = " + variableCount);
    }

}
