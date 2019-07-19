/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.barvinok;

import org.apache.commons.exec.CommandLine;
import org.apache.commons.exec.DefaultExecutor;
import org.apache.commons.exec.PumpStreamHandler;
import org.apache.logging.log4j.Logger;
import org.apfloat.Apint;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.service.CountService;
import za.ac.sun.cs.green.util.Reporter;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;
import java.util.Random;
import java.util.Set;
import java.util.Stack;

/**
 * Barvinok command-line parametric count service. Instead of straightforwardly
 * computing the number of models that satisfy a system of constraints, this
 * service computes a function that, when evaluated, gives the count of models.
 * 
 * The function is stored and re-evaluated when the solution for a similar set
 * of equations is requested.
 */
public class CountBarvinokParametricService extends CountService {

	// ======================================================================
	//
	// FIELDS
	//
	// ======================================================================

	/**
	 * Combination of the Barvinok parametric executable, options, and the filename,
	 * all separated by spaces.
	 */
	private final String barvinokParametricCommand;

	/*
	 * Contains the model to use for the expression evaluator
	 */
	protected static final Map<IntVariable, Object> MODEL_MAPPING = new HashMap<IntVariable, Object>();;

	/*
	 * Keep track of all the variables in a formula. The use is for look-ups in the
	 * MODEL_MAPPING for the evaluator.
	 */
	protected static HashMap<IntVariable, Boolean> vars;

	/*
	 * Store all the bound variables of the formula
	 */
	protected static ArrayList<IntVariable> bounds;

	// ======================================================================
	//
	// CONSTRUCTOR & METHODS
	//
	// ======================================================================

	/**
	 * Construct an instance of the Barvinok parametric command-line counting service.
	 * 
	 * @param solver
	 *                   associated Green solver
	 * @param properties
	 *                   properties used to construct the service
	 */
	public CountBarvinokParametricService(Green solver, Properties properties) {
		super(solver);
		String p = properties.getProperty("green.barvinok_parametric.path");
		String a = properties.getProperty("green.barvinok_parametric.args");
		barvinokParametricCommand = p + ' ' + a;
		log.trace("barvinokParametricCommand={}", barvinokParametricCommand);
	}

	/**
	 *
	 *
	 * @param instance
	 * @return
	 *
	 * @see za.ac.sun.cs.green.service.CountService#count(za.ac.sun.cs.green.Instance)
	 */
	@Override
	protected Apint count(Instance instance) {
		String result = "";
		vars = new HashMap<>();
		bounds = new ArrayList<>();
		HashMap<Expression, Expression> cases = null;

		try {
			// translate to barvinok & add bounds
			result = translate(instance);
			
			// invoke barvinok
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
//						store.put(instance.getFullExpression().getString(), cases);
				store.put(instance.getFullExpression().toString(), cases);
			}
		} catch (TranslatorUnsupportedOperation x) {
			log.warn(x.getMessage(), x);
		} catch (VisitorException x) {
			log.fatal("encountered an exception -- this should not be happening!", x);
		}

		try {
			// extract bounds
			BoundsVisitor bv = new BoundsVisitor(vars, bounds, MODEL_MAPPING);

			instance.getFullExpression().accept(bv);
		} catch (VisitorException e) {
			e.printStackTrace();
		}

		// evaluate formulas
		EvaluatorVisitor evaluator = new EvaluatorVisitor(MODEL_MAPPING);
		try {
			assert (cases != null);
			for (Expression k : cases.keySet()) {
				k.accept(evaluator);
				if (evaluator.isSat()) {
					cases.get(k).accept(evaluator);
				}
			}
		} catch (VisitorException e) {
			e.printStackTrace();
		}

		// return count
		return new Apint(evaluator.getCount());
	}

	/**
	 * Stores the input in a file, invokes barvinok on the file, captures and
	 * processes the output, and returns the number of satisfying solutions as a
	 * string.
	 *
	 * @param input
	 *              the Barvinok input
	 * @return the number of satisfying solutions as a string
	 */
	private String invokeISCC(String input) {
		String result = "";
		try {
			// First store the input in a file
//			File file = new File(FILENAME);
//			if (file.exists()) {
//				file.delete();
//			}
//			file.createNewFile();
//			FileWriter writer = new FileWriter(file);
//			writer.write(input);
//			writer.close();
//			// Now invoke Barvinok
			ByteArrayOutputStream outputStream = new ByteArrayOutputStream();
			DefaultExecutor executor = new DefaultExecutor();
			executor.setStreamHandler(new PumpStreamHandler(outputStream));
//			executor.setWorkingDirectory(new File(directory));
			executor.setExitValues(null);
			executor.execute(CommandLine.parse(barvinokParametricCommand));
			result = outputStream.toString();
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
	public Object allChildrenDone(Instance instance, Object result) {
		return instance.getData(getClass());
	}

}

class EvaluatorVisitor extends Visitor {

	private Stack<Object> stack = new Stack<>();
	private Map<IntVariable, Object> modelMapping;

	EvaluatorVisitor(Map<IntVariable, Object> modelMapping) {
		this.modelMapping = modelMapping;
	}

	public Boolean isSat() {
		return (Boolean) stack.pop();
	}

	public Integer getCount() {
		Object x = stack.pop();
		if (x instanceof Integer) {
			return (Integer) x;
		} else {
			return ((Double) x).intValue();
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

		Boolean isSat = false;
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

		// apply operation
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
			assert (leftD != null && rightD != null);

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
			assert (leftD != null && rightD != null);

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
			assert (leftD != null && rightD != null);

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
				if (r instanceof Integer) {
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
			assert (leftD != null && rightD != null);

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
			assert (leftD != null && rightD != null);

			stack.push(leftD - rightD);
			break;
		case LE:
			if (((l instanceof Integer) || (l instanceof Double))
					&& ((r instanceof Integer) || (r instanceof Double))) {
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

				isSat = (leftD <= rightD);
				stack.push(isSat);
			} else if (((l instanceof Integer) || (l instanceof Double)) && (r instanceof Boolean)) {
				assert operation.getOperand(1) instanceof Operation;

				Operation rOperation = (Operation) operation.getOperand(1);
				// Operation.Operator rOperator = rOperation.getOperator();

//                    assert (rOperation.toString().equals(op.LE.toString())) || (rOperation.toString().equals(op.LE.toString()));
//                    assert rOperation.getOperand(0) instanceof IntVariable;

				if (l instanceof Integer) {
					leftD = new Double((Integer) l);
				} else {
					leftD = (Double) l;
				}

				rightD = getVariableValue((IntVariable) rOperation.getOperand(0));
				boolean rightD2 = (Boolean) r;
				isSat = (leftD <= rightD) && rightD2;
				stack.push(isSat);
			} else if ((l instanceof Boolean) && ((r instanceof Integer) || (r instanceof Double))) {
				assert operation.getOperand(0) instanceof Operation;

				Operation lOperation = (Operation) operation.getOperand(0);
				// Operation.Operator lOperator = lOperation.getOperator();

//                    assert (lOperation.toString().equals(op.LE.toString())) || (lOperation.toString().equals(op.LE.toString()));
//                    assert lOperation.getOperand(0) instanceof IntVariable;

				leftB = (Boolean) l;
				leftD = getVariableValue((IntVariable) lOperation.getOperand(1));
				Double rightD2;

				if (r instanceof Integer) {
					rightD2 = new Double((Integer) r);
				} else {
					rightD2 = (Double) r;
				}

				isSat = (leftD <= rightD2) && leftB;
				stack.push(isSat);
			} else {
				throw new RuntimeException("case not expected");
			}
			break;
		case OR:
			leftB = (Boolean) l;
			rightB = (Boolean) r;
			assert (leftB != null && rightB != null);

			isSat = (leftB || rightB);
			stack.push(isSat);
			break;
		case AND:
			leftB = (Boolean) l;
			rightB = (Boolean) r;
			assert (leftB != null && rightB != null);

			isSat = (leftB && rightB);
			stack.push(isSat);
			break;
		case NOT:
			if (l != null) {
				leftB = (Boolean) l;
				isSat = !leftB;

			} else if (r != null) {
				rightB = (Boolean) r;
				isSat = !rightB;
			}

			stack.push(isSat);
			break;
		case EQ:
			if (((l instanceof Integer) || (l instanceof Double))
					&& ((r instanceof Integer) || (r instanceof Double))) {
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

				isSat = (leftD.equals(rightD));
				stack.push(isSat);
			} else if (((l instanceof Integer) || (l instanceof Double)) && (r instanceof Boolean)) {
				assert operation.getOperand(1) instanceof Operation;

				Operation rOperation = (Operation) operation.getOperand(1);
				// Operation.Operator rOperator = rOperation.getOperator();

//                    assert (rOperation.toString().equals(op.EQ.toString())) || (rOperation.toString().equals(op.EQ.toString()));
//                    assert rOperation.getOperand(0) instanceof IntVariable;

				if (l instanceof Integer) {
					leftD = new Double((Integer) l);
				} else {
					leftD = (Double) l;
				}

				rightD = getVariableValue((IntVariable) rOperation.getOperand(0));
				boolean rightD2 = (Boolean) r;

				isSat = (leftD.equals(rightD)) && rightD2;
				stack.push(isSat);
			} else if ((l instanceof Boolean) && ((r instanceof Integer) || (r instanceof Double))) {
				assert operation.getOperand(0) instanceof Operation;

				Operation lOperation = (Operation) operation.getOperand(0);
				// Operation.Operator lOperator = lOperation.getOperator();

//                    assert (lOperation.toString().equals(op.EQ.toString())) || (lOperation.toString().equals(op.EQ.toString()));
//                    assert lOperation.getOperand(0) instanceof IntVariable;
				leftB = (Boolean) l;
				leftD = getVariableValue((IntVariable) lOperation.getOperand(1));
				Double rightD2;
				if (r instanceof Integer) {
					rightD2 = new Double((Integer) r);
				} else {
					rightD2 = (Double) r;
				}
				isSat = (leftD.equals(rightD2)) && leftB;
				stack.push(isSat);
			} else {
				throw new RuntimeException("case not expected");
			}
			break;
		case GE:
			if (((l instanceof Integer) || (l instanceof Double))
					&& ((r instanceof Integer) || (r instanceof Double))) {
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

				isSat = (leftD >= rightD);
				stack.push(isSat);
			} else if (((l instanceof Integer) || (l instanceof Double)) && (r instanceof Boolean)) {
				assert operation.getOperand(1) instanceof Operation;

				Operation rOperation = (Operation) operation.getOperand(1);
				// Operation.Operator rOperator = rOperation.getOperator();

//                    assert (rOperation.toString().equals(op.GE.toString())) || (rOperation.toString().equals(op.GE.toString()));
//                    assert rOperation.getOperand(0) instanceof IntVariable;

				if (l instanceof Integer) {
					leftD = new Double((Integer) l);
				} else {
					leftD = (Double) l;
				}

				rightD = getVariableValue((IntVariable) rOperation.getOperand(0));
				boolean rightD2 = (Boolean) r;
				isSat = (leftD >= rightD) && rightD2;
				stack.push(isSat);
			} else if ((l instanceof Boolean) && ((r instanceof Integer) || (r instanceof Double))) {
				assert operation.getOperand(0) instanceof Operation;

				Operation lOperation = (Operation) operation.getOperand(0);
				// Operation.Operator lOperator = lOperation.getOperator();

//                    assert (lOperation.toString().equals(op.GE.toString())) || (lOperation.toString().equals(op.GE.toString()));
//                    assert lOperation.getOperand(0) instanceof IntVariable;

				leftB = (Boolean) l;
				leftD = getVariableValue((IntVariable) lOperation.getOperand(1));
				Double rightD2;

				if (r instanceof Integer) {
					rightD2 = new Double((Integer) r);
				} else {
					rightD2 = (Double) r;
				}

				isSat = (leftD >= rightD2) && leftB;
				stack.push(isSat);
			} else {
				throw new RuntimeException("case not expected");
			}
			break;
		case LT:
			if (((l instanceof Integer) || (l instanceof Double))
					&& ((r instanceof Integer) || (r instanceof Double))) {
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

				isSat = (leftD < rightD);
				stack.push(isSat);
			} else if (((l instanceof Integer) || (l instanceof Double)) && (r instanceof Boolean)) {
				assert operation.getOperand(1) instanceof Operation;

				Operation rOperation = (Operation) operation.getOperand(1);
				// Operation.Operator rOperator = rOperation.getOperator();

//                    assert (rOperation.toString().equals(op.LT.toString())) || (rOperation.toString().equals(op.LT.toString()));
//                    assert rOperation.getOperand(0) instanceof IntVariable;

				if (l instanceof Integer) {
					leftD = new Double((Integer) l);
				} else {
					leftD = (Double) l;
				}

				rightD = getVariableValue((IntVariable) rOperation.getOperand(0));
				boolean rightD2 = (Boolean) r;
				isSat = (leftD < rightD) && rightD2;
				stack.push(isSat);
			} else if ((l instanceof Boolean) && ((r instanceof Integer) || (r instanceof Double))) {
				assert operation.getOperand(0) instanceof Operation;

				Operation lOperation = (Operation) operation.getOperand(0);
				// Operation.Operator lOperator = lOperation.getOperator();

//                    assert (lOperation.toString().equals(op.LT.toString())) || (lOperation.toString().equals(op.LT.toString()));
//                    assert lOperation.getOperand(0) instanceof IntVariable;

				leftB = (Boolean) l;
				leftD = getVariableValue((IntVariable) lOperation.getOperand(1));
				Double rightD2;

				if (r instanceof Integer) {
					rightD2 = new Double((Integer) r);
				} else {
					rightD2 = (Double) r;
				}

				isSat = (leftD < rightD2) && leftB;
				stack.push(isSat);
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
			assert (leftD != null && rightD != null);

			isSat = (!leftD.equals(rightD));
			stack.push(isSat);
			break;
		case GT:
			if (((l instanceof Integer) || (l instanceof Double))
					&& ((r instanceof Integer) || (r instanceof Double))) {
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

				isSat = (leftD > rightD);
				stack.push(isSat);
			} else if (((l instanceof Integer) || (l instanceof Double)) && (r instanceof Boolean)) {
				assert operation.getOperand(1) instanceof Operation;

				Operation rOperation = (Operation) operation.getOperand(1);
				// Operation.Operator rOperator = rOperation.getOperator();

//                    assert (rOperation.toString().equals(op.GT.toString())) || (rOperation.toString().equals(op.GT.toString()));
//                    assert rOperation.getOperand(0) instanceof IntVariable;

				if (l instanceof Integer) {
					leftD = new Double((Integer) l);
				} else {
					leftD = (Double) l;
				}

				rightD = getVariableValue((IntVariable) rOperation.getOperand(0));
				boolean rightD2 = (Boolean) r;
				isSat = (leftD > rightD) && rightD2;
				stack.push(isSat);
			} else if ((l instanceof Boolean) && ((r instanceof Integer) || (r instanceof Double))) {
				assert operation.getOperand(0) instanceof Operation;

				Operation lOperation = (Operation) operation.getOperand(0);
				// Operation.Operator lOperator = lOperation.getOperator();

//                    assert (lOperation.toString().equals(op.GT.toString())) || (lOperation.toString().equals(op.GT.toString()));
//                    assert lOperation.getOperand(0) instanceof IntVariable;

				leftB = (Boolean) l;
				leftD = getVariableValue((IntVariable) lOperation.getOperand(1));
				Double rightD2;

				if (r instanceof Integer) {
					rightD2 = new Double((Integer) r);
				} else {
					rightD2 = (Double) r;
				}

				isSat = (leftD > rightD2) && leftB;
				stack.push(isSat);
			} else {
				throw new RuntimeException("case not expected");
			}
			break;
		default:
			break;
		}
	}

	private Double getVariableValue(IntVariable variable) {
		// changed from linear search to single map call.
		return new Double((Integer) modelMapping.get(variable));
	}

}

class BoundsVisitor extends Visitor {

	private HashMap<IntVariable, Boolean> vars;
	private ArrayList<IntVariable> bounds;
	private Map<IntVariable, Object> modelMapping;

	BoundsVisitor(HashMap<IntVariable, Boolean> vars, ArrayList<IntVariable> bounds,
			Map<IntVariable, Object> modelMapping) {
		super();
		this.vars = vars;
		this.bounds = bounds;
		this.modelMapping = modelMapping;
	}

	@Override
	public void postVisit(Variable variable) throws VisitorException {
		super.postVisit(variable);

		if (vars.get((IntVariable) variable) == null) { // changed from linear search, to single map call.
			// if variable has not been seen yet (i.e. not in map == null):
			// add the unique variables to the list
			vars.put((IntVariable) variable, true);

			// Extract bounds
			Integer lower = ((IntVariable) variable).getLowerBound();
			Integer upper = ((IntVariable) variable).getUpperBound();

			IntVariable lowerVar = new IntVariable(variable.toString() + "min", lower, lower);
			IntVariable upperVar = new IntVariable(variable.toString() + "max", upper, upper);

			bounds.add(lowerVar);
			bounds.add(upperVar);

			modelMapping.put(lowerVar, lower);
			modelMapping.put(upperVar, upper);
		}
	}
}
