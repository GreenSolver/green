package za.ac.sun.cs.green.service.barvinok;

import za.ac.sun.cs.green.expr.*;
import za.ac.sun.cs.green.parser.isl.Parser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Stack;

/**
 * @date: 2018/11/21
 * @author: JH Taljaard.
 * @contributer: Jaco Geldenhuys
 *
 * Description:
 * Translator for isl output
 */
public class ISLTranslator {

    protected Stack<Object> stack = null;
    protected ArrayList<IntVariable> vars = null;
    protected ArrayList<IntVariable> bounds = null;

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
    public HashMap<Expression, Expression> translate(String input) {
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
        ISLVisitor islVisitor = new ISLVisitor(stack, vars);
        expression.accept(islVisitor);
        StringBuilder ans = new StringBuilder();
        // start expression
        String queryName = "P";
        ans.append(queryName).append(" := "); // declare query

        // prepend bounds variables
        if (vars != null) {
            // declare bounds
            ans.append("[");
            constructBounds(vars, bounds);
            int n = bounds.size()-1; // leaving the last one
            for (int i = 0; i < n; i++) {
                ans.append(bounds.get(i));
                ans.append(",");
            }
            // end bounds declaration
            ans.append(bounds.get(n)); // adds last element
            // end variable declarations
            ans.append("] ");
            ans.append(" -> ");
        } // else

        // start consraints
        ans.append("{");

        // declare variables
        String varDecl = addVarDecls(vars, bounds);
        ans.append(varDecl);

        while (!stack.empty()) {
            ans.append(stack.pop());
        }

        assert stack.isEmpty();

        // add bounds
        String boundDecl = addBounds(vars, bounds);
        ans.append(boundDecl);

        ans.append("};\n"); // close function
        ans.append("card ").append(queryName).append(";"); // calculate cardinality

        return ans.toString();
    }

    private void constructBounds(ArrayList<IntVariable> vars, ArrayList<IntVariable> bounds) {
        for (IntVariable x : vars) {
            IntVariable upper = new IntVariable(x.getString() + "min",0,0);
            IntVariable lower = new IntVariable(x.getString() + "max",0,0);

            bounds.add(upper);
            bounds.add(lower);
        }
    }

    private String addVarDecls(ArrayList<IntVariable> vars, ArrayList<IntVariable> bounds) {
        StringBuilder varDecl = new StringBuilder();
        varDecl.append("[");
        int n = vars.size()-1;
        for (int i = 0; i < n; i++) {
            varDecl.append(vars.get(i));
            varDecl.append(",");
        }
        varDecl.append(vars.get(n));
        // end variable declarations
        varDecl.append("] : ");
        return varDecl.toString();
    }

    private String addBounds(ArrayList<IntVariable> vars, ArrayList<IntVariable> bounds) {
        StringBuilder bound = new StringBuilder();
        int j = 0;
        for (IntVariable var : vars) {
            bound.append(" and (").append(bounds.get(j).getString()).append(" <= ").append(var.getString()).append(" <= ").append(bounds.get(j + 1)).append(")");
            j = j + 2;
        }
        return bound.toString();
    }
}

class ISLVisitor extends Visitor {

    private Stack<Object> stack;
    private ArrayList<IntVariable> vars;

    public ISLVisitor(Stack<Object> stack, ArrayList<IntVariable> vars) {
        this.stack = stack;
        this.vars = vars;
    }

    @Override
    public void postVisit(IntConstant constant) {
        stack.push(constant.getValue());
    }

    @Override
    public void postVisit(IntVariable variable) {
        if (!vars.contains(variable)) {
            vars.add(variable);
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
