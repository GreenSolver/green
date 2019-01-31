package za.ac.sun.cs.green.service.barvinok;

import org.apache.commons.exec.CommandLine;
import org.apache.commons.exec.DefaultExecutor;
import org.apache.commons.exec.ExecuteException;
import org.apache.commons.exec.PumpStreamHandler;
import org.apache.logging.log4j.Logger;
import org.apfloat.Apint;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.*;
import za.ac.sun.cs.green.service.BasicService;
import za.ac.sun.cs.green.util.Reporter;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.text.SimpleDateFormat;
import java.util.*;

/**
 * @date: 2017/07/26
 * @author: JH Taljaard.
 * Student Number: 18509193.
 * Mentor: Willem Visser
 * Supervisor: Jaco Geldenhuys
 *
 * Description:
 * Get the recurring function from Barvinok.
 * Use the recurring function to calculate the SAT count value.
 * Stores the recurring function for reuse.
 *
 * [Dependency]
 * -    Barvinok library installation: http://barvinok.gforge.inria.fr/
 *      Which depends on:
 *      || GMP: https://gmplib.org/list-archives/gmp-announce/2014-March/000042.html
 *      || NTL: 
 * -    A script file (barviscc) is needed to pass the input from the Sevice to Barvinok.
 *      The iscc tool of Barvinok is called to get the recurring function.
 *
 * Script file (basic):
 * /path/to/iscc < $1
 *
 * Script file (verbose):
 * ############################################
 * #!/bin/sh
 *
 * WORKDIR=/full/path/to/lib/barvinok-0.39
 * FILE=${1}
 * OUTFILE=${WORKDIR}/`basename ${FILE}`.`date +'%s'`
 *
 * cat ${FILE} > ${OUTFILE}.original
 * ${WORKDIR}/iscc < ${FILE} > ${OUTFILE}.postiscc
 * cat ${OUTFILE}.postiscc
 * ###########################################
 *
 * The DEFAULT_BARVENUM_PATH must be appropriately updated such that it points to
 * <isccpath> the script file.
 */
public class BarvinokEnumerateService extends BasicService {

    private static final Boolean DEBUG = false;

    private static final String DIRECTORY = System.getProperty("java.io.tmpdir");

    private static final String DATE = new SimpleDateFormat("yyyyMMdd-HHmmss-SSS").format(new Date());

    private static final int RANDOM = new Random().nextInt(9);

    private static final String DIRNAME = String.format("%s/%s%s", DIRECTORY, DATE, RANDOM);

    private static String directory = null;

    static {
        File d = new File(DIRNAME);
        if (!d.exists()) {
            if (d.mkdir()) {
                directory = DIRNAME;
            } else {
                directory = DIRECTORY;
            }
        }
    }

    /*
     * File where the iscc input is stored.
     */
    private static final String FILENAME = directory + "/iscc-barvinok.in";

    /*
     * The location of the iscc executable file.
     */
    private final String DEFAULT_BARVENUM_PATH;
    private final String BARVENUM_PATH = "barvinokisccpath";
    private final String resourceName = "build.properties";

    /*
     * Options passed to the Barvinok executable.
     */
    private final String DEFAULT_BARVINOK_ARGS = " ";

    /*
     * Combination of the Barvinok executable, options, and the filename, all
     * separated by spaces.
     */
    private final String barvinokCommand;

    /*
     * Logger.
     */
    private Logger log;

    /*
     ##################################################################
     #################### For logging purposes ########################
     ##################################################################
    */

    /*
     * Execution Time of the service.
     */
    private long timeConsumption = 0;

    /*
     * Total number of times a formula is retrieved from Redis.
     */
    private static int cacheHitCount = 0;

    /*
     * Total number of times a formula is not in Redis.
     */
    private static int cacheMissCount = 0;

    /*
     * Total number of time the service is invoked.
     */
    private int invocationCount = 0;

    /*##################################################################*/

    /*
     * Contains the model to use for the expression evaluator
     */
    protected static Map<IntVariable, Object> MODEL_MAPPING;

    /*
     * Keep track of all the variables in a formula.
     * The use is for look-ups in the MODEL_MAPPING
     * for the evaluator.
     */
    protected static ArrayList<IntVariable> vars;

    /*
     * Store all the bound variables of the formula
     */
    protected static ArrayList<IntVariable> bounds;

    public BarvinokEnumerateService(Green solver, Properties properties) {
        super(solver);
        log = solver.getLogger();

        String barvPath = new File("").getAbsolutePath() + "/lib/barvinok-0.39/barviscc";
        ClassLoader loader = Thread.currentThread().getContextClassLoader();
        InputStream resourceStream;
        try {
            resourceStream = loader.getResourceAsStream(resourceName);
            if (resourceStream == null) {
                // If properties are correct, override with that specified path.
                resourceStream = new FileInputStream((new File("").getAbsolutePath()) + "/" + resourceName);

            }
            if (resourceStream != null) {
                properties.load(resourceStream);
                barvPath = properties.getProperty(BARVENUM_PATH);
                resourceStream.close();
            }
        } catch (IOException x) {
            // ignore
        }

        DEFAULT_BARVENUM_PATH = barvPath;

        String p = properties.getProperty("green.barvinok.path", BARVENUM_PATH);
        String a = properties.getProperty("green.barvinok.args", DEFAULT_BARVINOK_ARGS);
        barvinokCommand = p + ' ' + a + FILENAME;

        log.debug("barvinokCommand=" + barvinokCommand);
        log.debug("directory=" + directory);
    }

    @Override
    public Object allChildrenDone(Instance instance, Object result) {
        return instance.getData(getClass());
    }

    @Override
    public Set<Instance> processRequest(Instance instance) {
        Apint result = (Apint) instance.getData(getClass());
        if (result == null) {
            result = solve(instance);
            if (result != null) {
                instance.setData(getClass(), result);
            }
        }
        return null;
    }

    protected Apint solve(Instance instance) {
        invocationCount++;
        long startTime = System.currentTimeMillis();
        Apint count = null;

        count = solve0(instance);
        timeConsumption += System.currentTimeMillis() - startTime;

        return count;
    }

    private Apint solve0(Instance instance) {
        String result = "";
        vars = new ArrayList<>();
        bounds = new ArrayList<>();
        MODEL_MAPPING = new HashMap<IntVariable, Object>();
        HashMap<Expression, Expression> cases = null;

        if (store != null) {
            //check in store
            cases = (HashMap<Expression, Expression>) store.get(instance.getFullExpression().toString());

            if (cases == null) {
                //  not in store
                cacheMissCount++;
                try {
                    //  translate to barvinok & add bounds
                    result = translate(instance);

                    //  invoke barvinok
                    result = invokeISCC(result);

                    if (result.startsWith("{", 0)) {
                        // has count
                        int lastBracket = result.lastIndexOf('}');
                        result = result.substring(1, lastBracket).trim();
                    } else if (result.startsWith("[", 0)) {
                        // has formula
                        // translate (to green)
                        cases = translate(result);

                        // add to store
                        // key: query; value: case -> expression tree
                        store.put(instance.getFullExpression().toString(), cases);
                    }
                } catch (TranslatorUnsupportedOperation x) {
                    log.warn(x.getMessage(), x);
                } catch (VisitorException x) {
                    log.fatal("encountered an exception -- this should not be happening!", x);
                }
            } else {
                // else :: in store
                cacheHitCount++;
            }

        } else {
            // just call main stuff
            try {
                result = translate(instance);
                result = invokeISCC(result);
                if (result.startsWith("{", 0)) {
                    // has count
                    int lastBracket = result.lastIndexOf('}');
                    result = result.substring(1, lastBracket).trim();
                } else if (result.startsWith("[", 0)) {
                    // has formula
                    //  translate (to green)
                    cases = translate(result);
                }
            } catch (VisitorException e) {
                e.printStackTrace();
            }
        }

        try {
            //extract bounds
            BoundsVisitor bv = new BoundsVisitor();
            instance.getFullExpression().accept(bv);
        } catch (VisitorException e) {
            e.printStackTrace();
        }

        //evaluate formulas
        EvaluatorVisitor evaluator = new EvaluatorVisitor();
        try {
            for (Expression k : cases.keySet()) {
                k.accept(evaluator);
                if (evaluator.isSat()) {
                    cases.get(k).accept(evaluator);
                }
            }
        } catch (VisitorException e) {
            e.printStackTrace();
        }

        //return count
        return new Apint(evaluator.getCount());
    }

    /**
     * Stores the input in a file, invokes LattE on the file, captures and
     * processes the output, and returns the number of satisfying solutions
     * as a string.
     *
     * @param input
     *            the LattE input as an H-matrix
     * @return the number of satisfying solutions as a string
     */
    private String invokeISCC(String input) {
        String result = "";
        try {
            // First store the input in a file
            File file = new File(FILENAME);
            if (file.exists()) {
                file.delete();
            }
            file.createNewFile();
            FileWriter writer = new FileWriter(file);
            writer.write(input);
            writer.close();
            // Now invoke Barvinok
            ByteArrayOutputStream outputStream = new ByteArrayOutputStream();
            DefaultExecutor executor = new DefaultExecutor();
            executor.setStreamHandler(new PumpStreamHandler(outputStream));
            executor.setWorkingDirectory(new File(directory));
            executor.setExitValues(null);
            executor.execute(CommandLine.parse(barvinokCommand));
            result = outputStream.toString();
        } catch (ExecuteException e) {
            e.printStackTrace();
            throw new RuntimeException();
        } catch (IOException e) {
            e.printStackTrace();
            throw new RuntimeException();
        }
        return result;
    }

    private String translate(Instance instance) throws VisitorException {
        return new ISLTranslator().translate(instance.getFullExpression());
    }

    private HashMap<Expression, Expression> translate(String input) {
        return new ISLTranslator().translate(input);
    }

    @Override
    public void report(Reporter reporter) {
        reporter.report(getClass().getSimpleName(), "invocations = " + invocationCount);
        reporter.report(getClass().getSimpleName(), "cacheHitCount = " + cacheHitCount);
        reporter.report(getClass().getSimpleName(), "cacheMissCount = " + cacheMissCount);
        reporter.report(getClass().getSimpleName(), "timeConsumption = " + timeConsumption);
    }
}

class EvaluatorVisitor extends Visitor {

    Stack<Object> stack = new Stack<>();

    public Boolean isSat() {
        return (Boolean) stack.pop();
    }

    public Integer getCount() {
        Object x = stack.pop();
        if (x instanceof Integer) {
            return (Integer) x;
        } else {
            return new Integer(((Double) x).intValue());
        }
    }

    @Override
    public void postVisit(Expression expression) throws VisitorException {
        super.postVisit(expression);
    }

    @Override
    public void postVisit(Variable variable) throws VisitorException {
        super.postVisit(variable);
        stack.push(getVariableValue((IntVariable) variable));
    }

    @Override
    public void postVisit(Constant constant) throws VisitorException {
        super.postVisit(constant);
        stack.push(((IntConstant) constant).getValue());
    }

    @Override
    public void postVisit(Operation operation) throws VisitorException {
        super.postVisit(operation);

        Boolean SAT = false;
        Object l = null;
        Object r = null;

        int arity = operation.getOperator().getArity();
        if (arity == 2) {
            if (!stack.isEmpty()) {
                r = stack.pop();
            }
            if (!stack.isEmpty()) {
                l = stack.pop();
            }
        } else if (arity == 1) {
            if (!stack.isEmpty()) {
                l = stack.pop();
            }
        }

        Operation.Operator op = operation.getOperator();

        // Vars for casting
        Double leftD, rightD;
        Boolean leftB, rightB;

        switch (op) {
            case MUL:
                if (l instanceof Integer) {
                    leftD = new Double((Integer) l);
                } else {
                    leftD = (Double) l;
                }

                if (r instanceof Integer) {
                    rightD = new Double((Integer) r);
                } else {
                    rightD = (Double) r;
                }

                stack.push(leftD * rightD);
                break;
            case DIV:
                if (l instanceof Integer) {
                    leftD = new Double((Integer) l);
                } else {
                    leftD = (Double) l;
                }

                if (r instanceof Integer) {
                    rightD = new Double((Integer) r);
                } else {
                    rightD = (Double) r;
                }

                stack.push(leftD / rightD);
                break;
            case POWER:
                if (l instanceof Integer) {
                    leftD = new Double((Integer) l);
                } else {
                    leftD = (Double) l;
                }

                if (r instanceof Integer) {
                    rightD = new Double((Integer) r);
                } else {
                    rightD = (Double) r;
                }

                stack.push(Math.pow(leftD, rightD));
                break;
            case FLOOR:
                Double x = 0.0;

                if (l != null) {
                    if (l instanceof Integer) {
                        Double z = new Double((Integer) l);
                        x = Math.floor(z);
                    } else {
                        x = Math.floor((Double) l);
                    }
                } else if (r != null) {
                    if (l instanceof Integer) {
                        Double z = new Double((Integer) r);
                        x = Math.floor(z);
                    } else {
                        x = Math.floor((Double) r);
                    }
                }

                stack.push(x);
                break;
            case ADD:
                if (l instanceof Integer) {
                    leftD = new Double((Integer) l);
                } else {
                    leftD = (Double) l;
                }

                if (r instanceof Integer) {
                    rightD = new Double((Integer) r);
                } else {
                    rightD = (Double) r;
                }

                stack.push(leftD + rightD);
                break;
            case SUB:
                if (l instanceof Integer) {
                    leftD = new Double((Integer) l);
                } else {
                    leftD = (Double) l;
                }

                if (r instanceof Integer) {
                    rightD = new Double((Integer) r);
                } else {
                    rightD = (Double) r;
                }

                stack.push(leftD - rightD);
                break;
            case LE:
                if (((l instanceof Integer)||(l instanceof Double)) && ((r instanceof Integer)||(r instanceof Double))) {
                    if (l instanceof Integer) {
                        leftD = new Double((Integer) l);
                    } else {
                        leftD = (Double) l;
                    }

                    if (r instanceof Integer) {
                        rightD = new Double((Integer) r);
                    } else {
                        rightD = (Double) r;
                    }

                    SAT = (leftD <= rightD);
                    stack.push(SAT);
                } else if (((l instanceof Integer)||(l instanceof Double)) && (r instanceof Boolean)) {
                    assert operation.getOperand(1) instanceof Operation;

                    Operation rOperation = (Operation) operation.getOperand(1);
                    Operation.Operator rOperator = rOperation.getOperator();

                    assert (rOperation.toString().equals(op.LE.toString())) || (rOperation.toString().equals(op.LE.toString()));
                    assert rOperation.getOperand(0) instanceof IntVariable;

                    if (l instanceof Integer) {
                        leftD = new Double((Integer) l);
                    } else {
                        leftD = (Double) l;
                    }

                    rightD = getVariableValue((IntVariable) rOperation.getOperand(0));
                    boolean rightD2 = (Boolean) r;
                    SAT = (leftD <= rightD) && rightD2;
                    stack.push(SAT);
                } else if ((l instanceof Boolean) && ((r instanceof Integer)||(r instanceof Double))) {
                    assert operation.getOperand(0) instanceof Operation;

                    Operation lOperation = (Operation) operation.getOperand(0);
                    Operation.Operator lOperator = lOperation.getOperator();

                    assert (lOperation.toString().equals(op.LE.toString())) || (lOperation.toString().equals(op.LE.toString()));
                    assert lOperation.getOperand(0) instanceof IntVariable;

                    leftB = (Boolean) l;
                    leftD = getVariableValue((IntVariable) lOperation.getOperand(1));
                    Double rightD2;

                    if (r instanceof Integer) {
                        rightD2 = new Double((Integer) r);
                    } else {
                        rightD2 = (Double) r;
                    }

                    SAT = (leftD <= rightD2) && leftB;
                    stack.push(SAT);
                } else {
                    throw new RuntimeException("case not expected");
                }
                break;
            case OR:
                leftB = (Boolean) l;
                rightB = (Boolean) r;

                SAT = (leftB || rightB);
                stack.push(SAT);
                break;
            case AND:
                leftB = (Boolean) l;
                rightB = (Boolean) r;

                SAT = (leftB && rightB);
                stack.push(SAT);
                break;
            case NOT:
                if (l != null) {
                    leftB = (Boolean) l;
                    SAT = !leftB;

                } else if (r != null) {
                    rightB = (Boolean) r;
                    SAT = !rightB;
                }

                stack.push(SAT);
                break;
            case EQ:
                if (((l instanceof Integer)||(l instanceof Double)) && ((r instanceof Integer)||(r instanceof Double))) {
                    if (l instanceof Integer) {
                        leftD = new Double((Integer) l);
                    } else {
                        leftD = (Double) l;
                    }

                    if (r instanceof Integer) {
                        rightD = new Double((Integer) r);
                    } else {
                        rightD = (Double) r;
                    }

                    SAT = (leftD == rightD);
                    stack.push(SAT);
                } else if (((l instanceof Integer)||(l instanceof Double)) && (r instanceof Boolean)) {
                    assert operation.getOperand(1) instanceof Operation;

                    Operation rOperation = (Operation) operation.getOperand(1);
                    Operation.Operator rOperator = rOperation.getOperator();

                    assert (rOperation.toString().equals(op.EQ.toString())) || (rOperation.toString().equals(op.EQ.toString()));
                    assert rOperation.getOperand(0) instanceof IntVariable;

                    if (l instanceof Integer) {
                        leftD = new Double((Integer) l);
                    } else {
                        leftD = (Double) l;
                    }

                    rightD = getVariableValue((IntVariable) rOperation.getOperand(0));
                    boolean rightD2 = (Boolean) r;
                    SAT = (leftD == rightD) && rightD2;
                    stack.push(SAT);
                } else if ((l instanceof Boolean) && ((r instanceof Integer)||(r instanceof Double))) {
                    assert operation.getOperand(0) instanceof Operation;

                    Operation lOperation = (Operation) operation.getOperand(0);
                    Operation.Operator lOperator = lOperation.getOperator();

                    assert (lOperation.toString().equals(op.EQ.toString())) || (lOperation.toString().equals(op.EQ.toString()));
                    assert lOperation.getOperand(0) instanceof IntVariable;
                    leftB = (Boolean) l;
                    leftD = getVariableValue((IntVariable) lOperation.getOperand(1));
                    Double rightD2;
                    if (r instanceof Integer) {
                        rightD2 = new Double((Integer) r);
                    } else {
                        rightD2 = (Double) r;
                    }
                    SAT = (leftD == rightD2) && leftB;
                    stack.push(SAT);
                } else {
                    throw new RuntimeException("case not expected");
                }
                break;
            case GE:
                if (((l instanceof Integer)||(l instanceof Double)) && ((r instanceof Integer)||(r instanceof Double))) {
                    if (l instanceof Integer) {
                        leftD = new Double((Integer) l);
                    } else {
                        leftD = (Double) l;
                    }

                    if (r instanceof Integer) {
                        rightD = new Double((Integer) r);
                    } else {
                        rightD = (Double) r;
                    }

                    SAT = (leftD >= rightD);
                    stack.push(SAT);
                } else if (((l instanceof Integer)||(l instanceof Double)) && (r instanceof Boolean)) {
                    assert operation.getOperand(1) instanceof Operation;

                    Operation rOperation = (Operation) operation.getOperand(1);
                    Operation.Operator rOperator = rOperation.getOperator();

                    assert (rOperation.toString().equals(op.GE.toString())) || (rOperation.toString().equals(op.GE.toString()));
                    assert rOperation.getOperand(0) instanceof IntVariable;

                    if (l instanceof Integer) {
                        leftD = new Double((Integer) l);
                    } else {
                        leftD = (Double) l;
                    }

                    rightD = getVariableValue((IntVariable) rOperation.getOperand(0));
                    boolean rightD2 = (Boolean) r;
                    SAT = (leftD >= rightD) && rightD2;
                    stack.push(SAT);
                } else if ((l instanceof Boolean) && ((r instanceof Integer)||(r instanceof Double))) {
                    assert operation.getOperand(0) instanceof Operation;

                    Operation lOperation = (Operation) operation.getOperand(0);
                    Operation.Operator lOperator = lOperation.getOperator();

                    assert (lOperation.toString().equals(op.GE.toString())) || (lOperation.toString().equals(op.GE.toString()));
                    assert lOperation.getOperand(0) instanceof IntVariable;

                    leftB = (Boolean) l;
                    leftD = getVariableValue((IntVariable) lOperation.getOperand(1));
                    Double rightD2;

                    if (r instanceof Integer) {
                        rightD2 = new Double((Integer) r);
                    } else {
                        rightD2 = (Double) r;
                    }

                    SAT = (leftD >= rightD2) && leftB;
                    stack.push(SAT);
                } else {
                    throw new RuntimeException("case not expected");
                }
                break;
            case LT:
                if (((l instanceof Integer)||(l instanceof Double)) && ((r instanceof Integer)||(r instanceof Double))) {
                    if (l instanceof Integer) {
                        leftD = new Double((Integer) l);
                    } else {
                        leftD = (Double) l;
                    }

                    if (r instanceof Integer) {
                        rightD = new Double((Integer) r);
                    } else {
                        rightD = (Double) r;
                    }

                    SAT = (leftD < rightD);
                    stack.push(SAT);
                } else if (((l instanceof Integer)||(l instanceof Double)) && (r instanceof Boolean)) {
                    assert operation.getOperand(1) instanceof Operation;

                    Operation rOperation = (Operation) operation.getOperand(1);
                    Operation.Operator rOperator = rOperation.getOperator();

                    assert (rOperation.toString().equals(op.LT.toString())) || (rOperation.toString().equals(op.LT.toString()));
                    assert rOperation.getOperand(0) instanceof IntVariable;

                    if (l instanceof Integer) {
                        leftD = new Double((Integer) l);
                    } else {
                        leftD = (Double) l;
                    }

                    rightD = getVariableValue((IntVariable) rOperation.getOperand(0));
                    boolean rightD2 = (Boolean) r;
                    SAT = (leftD < rightD) && rightD2;
                    stack.push(SAT);
                } else if ((l instanceof Boolean) && ((r instanceof Integer)||(r instanceof Double))) {
                    assert operation.getOperand(0) instanceof Operation;

                    Operation lOperation = (Operation) operation.getOperand(0);
                    Operation.Operator lOperator = lOperation.getOperator();

                    assert (lOperation.toString().equals(op.LT.toString())) || (lOperation.toString().equals(op.LT.toString()));
                    assert lOperation.getOperand(0) instanceof IntVariable;

                    leftB = (Boolean) l;
                    leftD = getVariableValue((IntVariable) lOperation.getOperand(1));
                    Double rightD2;

                    if (r instanceof Integer) {
                        rightD2 = new Double((Integer) r);
                    } else {
                        rightD2 = (Double) r;
                    }

                    SAT = (leftD < rightD2) && leftB;
                    stack.push(SAT);
                } else {
                    throw new RuntimeException("case not expected");
                }
                break;
            case NE:
                if (l instanceof Integer) {
                    leftD = new Double((Integer) l);
                } else {
                    leftD = (Double) l;
                }

                if (r instanceof Integer) {
                    rightD = new Double((Integer) r);
                } else {
                    rightD = (Double) r;
                }

                SAT = (leftD != rightD);
                stack.push(SAT);
                break;
            case GT:
                if (((l instanceof Integer)||(l instanceof Double)) && ((r instanceof Integer)||(r instanceof Double))) {
                    if (l instanceof Integer) {
                        leftD = new Double((Integer) l);
                    } else {
                        leftD = (Double) l;
                    }

                    if (r instanceof Integer) {
                        rightD = new Double((Integer) r);
                    } else {
                        rightD = (Double) r;
                    }

                    SAT = (leftD > rightD);
                    stack.push(SAT);
                } else if (((l instanceof Integer)||(l instanceof Double)) && (r instanceof Boolean)) {
                    assert operation.getOperand(1) instanceof Operation;

                    Operation rOperation = (Operation) operation.getOperand(1);
                    Operation.Operator rOperator = rOperation.getOperator();

                    assert (rOperation.toString().equals(op.GT.toString())) || (rOperation.toString().equals(op.GT.toString()));
                    assert rOperation.getOperand(0) instanceof IntVariable;

                    if (l instanceof Integer) {
                        leftD = new Double((Integer) l);
                    } else {
                        leftD = (Double) l;
                    }

                    rightD = getVariableValue((IntVariable) rOperation.getOperand(0));
                    boolean rightD2 = (Boolean) r;
                    SAT = (leftD > rightD) && rightD2;
                    stack.push(SAT);
                } else if ((l instanceof Boolean) && ((r instanceof Integer)||(r instanceof Double))) {
                    assert operation.getOperand(0) instanceof Operation;

                    Operation lOperation = (Operation) operation.getOperand(0);
                    Operation.Operator lOperator = lOperation.getOperator();

                    assert (lOperation.toString().equals(op.GT.toString())) || (lOperation.toString().equals(op.GT.toString()));
                    assert lOperation.getOperand(0) instanceof IntVariable;

                    leftB = (Boolean) l;
                    leftD = getVariableValue((IntVariable) lOperation.getOperand(1));
                    Double rightD2;

                    if (r instanceof Integer) {
                        rightD2 = new Double((Integer) r);
                    } else {
                        rightD2 = (Double) r;
                    }

                    SAT = (leftD > rightD2) && leftB;
                    stack.push(SAT);
                } else {
                    throw new RuntimeException("case not expected");
                }
                break;
            default:
                break;
        }
    }

    private Double getVariableValue(IntVariable variable) {
        int pos = BarvinokEnumerateService.bounds.indexOf((IntVariable) variable);
        Double value = 0.0;

        for (IntVariable key : BarvinokEnumerateService.MODEL_MAPPING.keySet()) {
            if (variable.toString().equals(key.toString())) {
                Integer x = (Integer) BarvinokEnumerateService.MODEL_MAPPING.get(key);
                value = new Double(x);
                break;
            }
        }

        return value;
    }

}

class BoundsVisitor extends Visitor {

    @Override
    public void postVisit(Variable variable) throws VisitorException {
        super.postVisit(variable);

        if (!BarvinokEnumerateService.vars.contains((IntVariable) variable)) {
            // add the unique variables to the list
            BarvinokEnumerateService.vars.add((IntVariable) variable);

            // Extract bounds
            int lower = ((IntVariable) variable).getLowerBound();
            int upper = ((IntVariable) variable).getUpperBound();

            IntVariable lowerVar = new IntVariable(variable.toString() + "min", lower, lower);
            IntVariable upperVar = new IntVariable(variable.toString() + "max", upper, upper);

            BarvinokEnumerateService.bounds.add(lowerVar);
            BarvinokEnumerateService.bounds.add(upperVar);

            BarvinokEnumerateService.MODEL_MAPPING.put(lowerVar, lower);
            BarvinokEnumerateService.MODEL_MAPPING.put(upperVar, upper);
        }
    }
}
