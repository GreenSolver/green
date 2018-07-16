package za.ac.sun.cs.green.service.barvinok;

import za.ac.sun.cs.green.expr.*;
import za.ac.sun.cs.green.parser.isl.Parser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Stack;

/**
 * @date: 2017/08/14
 * @author: JH Taljaard.
 * @contributer: Jaco Geldenhuys
 * Student Number: 18509193.
 *
 * Description:
 * Translator for isl output
 */
public class ISLTranslator {

    protected static Stack<Object> stack = null;
    protected static ArrayList<IntVariable> vars = null;
    protected static ArrayList<IntVariable> bounds = null;

    public ISLTranslator() {
        stack = new Stack<Object>();
        vars = new ArrayList<>();
        bounds = new ArrayList<>();
    }

    /**
     * Takes a string (in isl format) as input and parse
     * it to Green expressions. The output is a map of
     * cases to formulas.
     * @param input a String in isl format.
     * @return hashmap of cases to formulas.
     */
    public HashMap translate(String input) {
        Parser p = new Parser(input);
        p.parse();
        return p.getCases();
    }

    /**
     * Takes Green expression and translate to isl format
     * @param expression Green expression
     * @return String representation of Green expression in isl format.
     */
    public String translate(Expression expression) throws VisitorException {
        ISLVisitor islVisitor = new ISLVisitor();
        expression.accept(islVisitor);
        int i = 0;
        StringBuilder ans = new StringBuilder();
        // start expression
        ans.append("P := "); // declare query

        // prepend bounds variables
        if (vars != null) {
            // declare bounds
            ans.append("[");
            constructBounds();
            for (i = 0; i < bounds.size()-1; i++) {
                ans.append(bounds.get(i));
                ans.append(",");
            }
            // end bounds declaration
            ans.append(bounds.get(bounds.size()-1));
            // end variable declarations
            ans.append("] ");
            ans.append(" -> ");
        } // else

        // start consraints
        ans.append("{");

        // declare variables
        ans.append("[");
        for (i = 0; i < vars.size()-1; i++) {
            ans.append(vars.get(i));
            ans.append(",");
        }
        ans.append(vars.get(vars.size()-1));
        // end variable declarations
        ans.append("] : ");

        while (!stack.empty()) {
            ans.append(stack.pop());
        }

        // add bounds
        String bounds = addBounds();
        ans.append(bounds);

        ans.append("};\n"); // close function
        ans.append("card P;"); // calculate cardinality

        assert stack.isEmpty();
        return ans.toString();
    }

    private void constructBounds() {
        for (IntVariable x : vars) {
            IntVariable upper = new IntVariable(x.toString()+"min",0,0);
            IntVariable lower = new IntVariable(x.toString()+"max",0,0);

            bounds.add(upper);
            bounds.add(lower);
        }
    }

    private String addBounds() {
        StringBuilder bound = new StringBuilder();
        int j = 0;
        for (IntVariable var : vars) {
            bound.append(" and (").append(bounds.get(j).toString()).append(" <= ").append(var.toString()).append(" <= ").append(bounds.get(j + 1)).append(")");
            j = j + 2;
        }
        return bound.toString();
    }
}

class ISLVisitor extends Visitor {

    private Stack<Object> stack = ISLTranslator.stack;
    private ArrayList<IntVariable> vars = ISLTranslator.vars;
    private ArrayList<IntVariable> bounds = ISLTranslator.bounds;

    @Override
    public void postVisit(IntConstant constant) {
        stack.push(constant.getValue());
    }

    @Override
    public void postVisit(IntVariable variable) {
        if (!vars.contains(variable)) {
            if (!bounds.contains(variable)) {
                vars.add(variable);
            }
        }
        stack.push(variable);
    }

    @Override
    public void postVisit(Operation operation) throws TranslatorUnsupportedOperation {
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

        switch (operation.getOperator()) {
            case EQ:
                stack.push(l + " = " + r);
                break;
            case NE:
                stack.push(l + " != " + r);
                break;
            case LT:
                stack.push(l + " < " + r);
                break;
            case LE:
                stack.push(l + " <= " + r);
                break;
            case GT:
                stack.push(l + " > " + r);
                break;
            case GE:
                stack.push(l + " >= " + r);
                break;
            case AND:
                stack.push("(" + l + " and " + r + ")");
                break;
            case ADD:
                stack.push(l + " + " + r);
                break;
            case SUB:
                stack.push(l + " - " + r);
                break;
            case MUL:
                stack.push(l + " * " + r);
                break;
            default:
                throw new TranslatorUnsupportedOperation("unsupported operation " + operation.getOperator());
        }
    }
}
