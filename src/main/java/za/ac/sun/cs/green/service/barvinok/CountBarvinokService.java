/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.service.barvinok;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.BitSet;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.stream.Collectors;

import org.apfloat.Apint;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.service.CountService;

/**
 * Barvinok command-line count service.
 */
public class CountBarvinokService extends CountService {

	// ======================================================================
	//
	// FIELDS
	//
	// ======================================================================

	/**
	 * Combination of the Barvinok executable, options, and the filename, all
	 * separated by spaces.
	 */
	protected final String barvinokCommand;

	// ======================================================================
	//
	// CONSTRUCTOR & METHODS
	//
	// ======================================================================

	/**
	 * Construct an instance of the Barvinok command-line counting service.
	 * 
	 * @param solver
	 *                   associated Green solver
	 * @param properties
	 *                   properties used to construct the service
	 */
	public CountBarvinokService(Green solver, Properties properties) {
		super(solver);
		String p = properties.getProperty("green.barvinok.path");
		String a = properties.getProperty("green.barvinok.args");
		barvinokCommand = p + ' ' + a;
		log.trace("barvinokCommand={}", barvinokCommand);
	}

	/**
	 * Do the work of converting an instance to a set of equations that Barvinok is
	 * prepared to accept, send the equations to Barvinok on the command line, and
	 * collect and return the result.
	 *
	 * @param instance
	 *                 problem to solve
	 * @return number of satisfying models for the problem
	 *
	 * @see za.ac.sun.cs.green.service.CountService#count(za.ac.sun.cs.green.Instance)
	 */
	@Override
	protected Apint count(Instance instance) {
		return new HMatrix().count(instance.getExpression());
	}

	// ======================================================================
	//
	// MATRIX ROWS
	//
	// ======================================================================

	/**
	 * A row that may appear in a matrix. It stores a mapping from variables to
	 * coefficients (and an additional, implicit mapping from the "
	 * <code>null</code>" variable to the constant coefficient that must appear in
	 * each row).
	 * 
	 * Each row has a type, which is a integer comparison (equal-to, not-equal-to,
	 * less-than, less-than-or-equal-to, greater-than, or greater-then-or-equal-to).
	 * Once all the coefficients have been entered, it is "fixed". This means that
	 * no new coefficients may be added, and some internal flags are set.
	 * 
	 */
	private static class HRow {

		/**
		 * Flag to indicate that the row has been fixed.
		 */
		private boolean fixed;

		/**
		 * Factor used to turn less-than and less-than-or-equal-to around.
		 */
		private int flip;

		/**
		 * The type of the row.
		 */
		private Operation.Operator type;

		/**
		 * The constant (i.e., variable-less) coefficient for the row.
		 */
		private int constantCoefficient;

		/**
		 * A mapping of variables to coefficients.
		 */
		private Map<IntVariable, Integer> coefficients;

		/**
		 * Constructor for the row.
		 * 
		 * @param type
		 *             the type of the row
		 */
		HRow(Operation.Operator type) {
			assert (type == Operation.Operator.EQ) || (type == Operation.Operator.NE) || (type == Operation.Operator.LT)
					|| (type == Operation.Operator.LE) || (type == Operation.Operator.GT)
					|| (type == Operation.Operator.GE);
			fixed = false;
			flip = 1;
			this.type = type;
			constantCoefficient = 0;
			coefficients = new HashMap<IntVariable, Integer>();
		}

		/**
		 * Adds a coefficient for the given variable. This overwrites any previous
		 * coefficient that might have been associated with a variable. If the given
		 * variable is <code>null</code>, the coefficient is taken to be the constant
		 * coefficient.
		 * 
		 * @param variable
		 *                    the variable
		 * @param coefficient
		 *                    the coefficient for the variable
		 */
		public void put(IntVariable variable, int coefficient) {
			assert !fixed;
			if (variable == null) {
				constantCoefficient = coefficient;
			} else {
				coefficients.put(variable, coefficient);
			}
		}

		/**
		 * Adds a coefficient for the given variable. This overwrites any previous
		 * coefficient that might have been associated with a variable. If the given
		 * variable is <code>null</code>, the coefficient is taken to be the constant
		 * coefficient.
		 * 
		 * @param variable
		 *                    the variable
		 * @param coefficient
		 *                    the coefficient for the variable
		 */
		public void put(IntVariable variable, IntConstant coefficient) {
			put(variable, coefficient.getValue());
		}

		/**
		 * Adds a value to the coefficient for a variable. If the variable has not yet
		 * been assigned a coefficient, the given value is taken to be the new
		 * coefficient. If the given variable is <code>null</code>, the coefficient is
		 * taken to be the constant coefficient.
		 * 
		 * @param variable
		 *                 the variable
		 * @param delta
		 *                 the value to add to the variable's coefficient
		 */
		public void add(IntVariable variable, int delta) {
			assert !fixed;
			if (variable == null) {
				constantCoefficient += delta;
			} else {
				Integer k = coefficients.get(variable);
				if (k == null) {
					coefficients.put(variable, delta);
				} else {
					coefficients.put(variable, k + delta);
				}
			}
		}

		/**
		 * Adds a value to the coefficient for a variable. If the variable has not yet
		 * been assigned a coefficient, the given value is taken to be the new
		 * coefficient. If the given variable is <code>null</code>, the coefficient is
		 * taken to be the constant coefficient.
		 * 
		 * @param variable
		 *                 the variable
		 * @param delta
		 *                 the value to add to the variable's coefficient
		 */
		@SuppressWarnings("unused")
		// Not used at the moment
		public void add(IntVariable variable, IntConstant delta) {
			add(variable, delta.getValue());
		}

		/**
		 * Finds the coefficient of the given variable. If the variable is
		 * <code>null</code>, the constant coefficient is returned. If the variable has
		 * no associated coefficient, the value 0 is returned.
		 * 
		 * @param variable
		 *                 the given variable
		 * @return the coefficient associated with the variable (or 0)
		 */
		public int get(IntVariable variable) {
			if (variable == null) {
				return flip * constantCoefficient;
			} else {
				Integer k = coefficients.get(variable);
				return (k != null) ? flip * k : 0;
			}
		}

		/**
		 * Fixes the row by adjusting the coefficients for rows of type greater-than,
		 * greater-than-or-equal, and less-than-or-equal, and changing their types to
		 * less-than.
		 */
		public void fix() {
			if (!fixed) {
				if (type == Operation.Operator.EQ) {
					flip = -1;
				} else if (type == Operation.Operator.NE) {
					flip = -1;
				} else if (type == Operation.Operator.LT) {
					flip = -1;
					add(null, 1);
					type = Operation.Operator.LE;
				} else if (type == Operation.Operator.LE) {
					flip = -1;
				} else if (type == Operation.Operator.GT) {
					add(null, -1);
					type = Operation.Operator.LE;
				} else if (type == Operation.Operator.GE) {
					type = Operation.Operator.LE;
				}
				fixed = true;
			}
		}

		/**
		 * Returns the set of variables that appear with non-zero coefficients in the
		 * row. The "<code>null</code>" constant coefficient variable is not returned.
		 * 
		 * @return the set of variables with non-zero coefficients
		 */
		public Set<IntVariable> getVariables() {
			assert fixed;
			return coefficients.keySet();
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see java.lang.Object#equals(java.lang.Object)
		 */
		@Override
		public boolean equals(Object object) {
			assert fixed;
			HRow row = (HRow) object;
			return (type == row.type) && (flip == row.flip) && (constantCoefficient == row.constantCoefficient)
					&& (coefficients.equals(row.coefficients));
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see java.lang.Object#hashCode()
		 */
		@Override
		public int hashCode() {
			return type.hashCode() ^ constantCoefficient ^ coefficients.hashCode();
		}

	}

	// ======================================================================
	//
	// MATRIX
	//
	// ======================================================================

	/**
	 * A representation of a conjunction of constraints. Each constraint is
	 * represented by an instance of an {@link HRow}. The rows are placed into sets
	 * based on their type. Once the sets have been populated, further internal
	 * calculation is used to take care of the inequality constraints which LattE
	 * cannot handle directly.
	 */
	private class HMatrix {

		/**
		 * The set of rows of the equal-to type.
		 */
		private final Set<HRow> eqRows = new HashSet<>();

		/**
		 * The set of rows of the not-equal-to type.
		 */
		private final Set<HRow> neRows = new HashSet<>();

		/**
		 * The set of rows of the less-than type.
		 */
		private final Set<HRow> ltRows = new HashSet<>();

		/**
		 * The set of variables that are present in all calls to LattE.
		 */
		private final Set<IntVariable> allVariables = new HashSet<>();

		/**
		 * The set of variables that are present in every call to LattE.
		 */
		private final Set<IntVariable> commonVariables = new HashSet<>();

		/**
		 * The number of times each variable occurs in the constraints that are present
		 * in every call to LattE.
		 */
		private final Map<IntVariable, Integer> commonOccurences = new HashMap<>();

		/**
		 * Number of difference values each variable can assume.
		 */
		private final Map<IntVariable, Apint> variableRange = new HashMap<>();

		/**
		 * The correction that is applied to subset results.
		 */
		private Apint correction;

		/**
		 * Constructs the rows of the matrix by recursively exploring the expression. It
		 * is assumed that the expression has a very specific form.
		 * 
		 * <pre>
		 * expr ::= constraint | expr && expr
		 * constraint ::= cexpr ( = | != | < | <= | > | >= ) 0
		 * cexpr ::= term | cexpr + term
		 * term ::= integer_constant | integer_constant * variable
		 * </pre>
		 * 
		 * @param operation
		 *                  the expression to explore
		 */
		private void explore(Operation operation) {
			Operation.Operator op = operation.getOperator();
			if (op == Operation.Operator.AND) {
				explore((Operation) operation.getOperand(0));
				explore((Operation) operation.getOperand(1));
			} else {
				assert (op == Operation.Operator.EQ) || (op == Operation.Operator.NE) || (op == Operation.Operator.LT)
						|| (op == Operation.Operator.LE) || (op == Operation.Operator.GT)
						|| (op == Operation.Operator.GE);
				HRow row = new HRow(op);
				int c = ((IntConstant) operation.getOperand(1)).getValue();
				assert (c == 0);
				Expression e = operation.getOperand(0);
				while ((e instanceof Operation) && (((Operation) e).getOperator() == Operation.Operator.ADD)) {
					explore0(row, ((Operation) e).getOperand(1));
					e = ((Operation) e).getOperand(0);
				}
				explore0(row, e);
				register(row);
			}
		}

		/**
		 * Processes one term of an expression and adding it to the given row. The term
		 * is assumed to have a very specific form.
		 * 
		 * <pre>
		 * term ::= integer_constant | integer_constant * variable
		 * </pre>
		 * 
		 * @param row
		 *                   the row to which the term information is added
		 * @param expression
		 *                   the term to process
		 */
		private void explore0(HRow row, Expression expression) {
			if (expression instanceof IntConstant) {
				int c = ((IntConstant) expression).getValue();
				row.put(null, c);
			} else {
				Operation o = (Operation) expression;
				assert o.getOperator() == Operation.Operator.MUL;
				row.put((IntVariable) o.getOperand(1), (IntConstant) o.getOperand(0));
			}
		}

		/**
		 * Register a row with the matrix by "fixing" it (by calling {@link HRow#fix()})
		 * and then adding it to the appropriate set, based on its type. The variables
		 * of the row is added to the set of variables.
		 * 
		 * @param row
		 *            the row to add to the matrix
		 */
		private void register(HRow row) {
			row.fix();
			Operation.Operator type = row.type;
			allVariables.addAll(row.getVariables());
			if (type == Operation.Operator.EQ) {
				eqRows.add(row);
				for (IntVariable v : row.getVariables()) {
					Integer o = commonOccurences.get(v);
					commonOccurences.put(v, o != null ? o + 1 : 1);
					commonVariables.add(v);
				}
			} else if (type == Operation.Operator.NE) {
				neRows.add(row);
			} else if (type == Operation.Operator.LE) {
				ltRows.add(row);
				for (IntVariable v : row.getVariables()) {
					Integer o = commonOccurences.get(v);
					commonOccurences.put(v, o != null ? o + 1 : 1);
					commonVariables.add(v);
				}
			} else {
				assert false;
			}
		}

		/**
		 * Counts the number solutions that satisfy the expression.
		 * 
		 * @param expression
		 *                   the expression to satisfy
		 * @return the number of satisfying solutions
		 */
		public Apint count(Expression expression) {
			explore((Operation) expression);
			for (IntVariable v : allVariables) {
				Apint x = new Apint(v.getUpperBound());
				variableRange.put(v, x.subtract(new Apint(v.getLowerBound())));
			}
			Apint n = Apint.ZERO;
			Subsetter<HRow> s = new Subsetter<HRow>(neRows);
			for (Set<HRow> ne = new HashSet<HRow>(); ne != null; ne = s.advance()) {
				if (ne.size() % 2 == 0) {
					n = n.add(processInput(generateConstraints(ne)));
				} else {
					n = n.subtract(processInput(generateConstraints(ne)));
				}
			}
			return n;
		}

		/**
		 * Convert the constraints captured by the matrix rows to a string.
		 *
		 * @param neRows rows to convert
		 * @return Barvinok input equivalent of rows as a string
		 */
		private String generateConstraints(Set<HRow> neRows) {
			// Now generate the constraints
			SortedSet<String> constraints = new TreeSet<String>();
			// Construct the set of variables and list of columns
			Set<IntVariable> variables = new HashSet<IntVariable>(commonVariables);
			List<IntVariable> columns = new LinkedList<IntVariable>(variables);
			final Map<IntVariable, Integer> occurences = new HashMap<IntVariable, Integer>(commonOccurences);
			for (HRow r : neRows) {
				for (IntVariable v : r.getVariables()) {
					Integer o = occurences.get(v);
					occurences.put(v, o != null ? o + 1 : 1);
					variables.add(v);
				}
			}
			Collections.sort(columns, new Comparator<IntVariable>() {

				@Override
				public int compare(IntVariable v1, IntVariable v2) {
					int k1 = occurences.get(v1);
					int k2 = occurences.get(v2);
					if (k1 < k2) {
						return -1;
					} else if (k1 > k2) {
						return 1;
					} else {
						return v1.compareTo(v2);
					}
				}
			});
			// Calculate the correction factor
			correction = Apint.ONE;
			for (IntVariable v : allVariables) {
				if (!variables.contains(v)) {
					correction = correction.multiply(variableRange.get(v));
				}
			}
			// Now we are ready to construct the constraints string, starting
			// with the less-than constraints
			for (HRow r : ltRows) {
				StringBuilder c = new StringBuilder();
				c.append('1');
				for (IntVariable v : columns) {
					c.append(' ').append(r.get(v));
				}
				c.append(' ').append(r.get(null));
				constraints.add(c.toString());
			}
			// Emit the equal-to constraints
			for (HRow r : eqRows) {
				StringBuilder c = new StringBuilder();
				c.append('0');
				for (IntVariable v : columns) {
					c.append(' ').append(r.get(v));
				}
				c.append(' ').append(r.get(null));
				String s = c.toString();
				constraints.add(s);
			}
			// Emit the not-equal-to constraints
			for (HRow r : neRows) {
				StringBuilder c = new StringBuilder();
				c.append('0');
				for (IntVariable v : columns) {
					c.append(' ').append(r.get(v));
				}
				c.append(' ').append(r.get(null));
				String s = c.toString();
				constraints.add(s);
			}
			// Construct the final string version
			int numColumns = columns.size() + 1;
			int numRows = constraints.size();
			StringBuilder c = new StringBuilder();
			c.append(numRows).append(' ');
			c.append(numColumns + 1).append('\n');
			for (String s : constraints) {
				c.append(s).append('\n');
			}
			return c.toString();
		}

		/**
		 * Processes the input to produce the number of satisfying solutions. If
		 * present, the store is checked first. If the answer is not already present, it
		 * is calculated and added to the store.
		 * 
		 * @param input
		 *              the LattE input as an H-matrix
		 * @return the number of satisfying solutions as an {@link Apint}
		 */
		private Apint processInput(String input) {
			if (store == null) {
				return new Apint(invokeBarvinok(input)).multiply(correction);
			} else {
				String count = store.getString(input);
				if (count == null) {
					count = invokeBarvinok(input);
					store.put(input, count);
				}
				return new Apint(count).multiply(correction);
			}
		}

		/**
		 * Stores the input in a file, invokes LattE on the file, captures and processes
		 * the output, and returns the number of satisfying solutions as a string.
		 * 
		 * @param input
		 *              the LattE input as an H-matrix
		 * @return the number of satisfying solutions as a string
		 */
		private String invokeBarvinok(String input) {
			try {
				log.trace("input: {}", input);
				Process process = Runtime.getRuntime().exec(barvinokCommand);
				OutputStream stdin = process.getOutputStream();
				InputStream stdout = process.getInputStream();
				BufferedReader outReader = new BufferedReader(new InputStreamReader(stdout));
				stdin.write((input + "\n").getBytes());
				stdin.flush();
				String output = outReader.readLine();
				if (!output.startsWith("POLYHEDRON")) {
					stdin.close();
					stdout.close();
					process.destroy();
					throw new RuntimeException();
				}
				stdin.close();
				output = outReader.lines().collect(Collectors.joining());
				stdout.close();
				process.destroy();
				log.trace("output: {}", output);
				int lastSpace = output.lastIndexOf(' ');
				int secondLastSpace = output.substring(0, lastSpace).lastIndexOf(' ');
				output = output.substring(secondLastSpace + 1, lastSpace);
				int newlineIndex = output.indexOf("\n");
				if (newlineIndex != -1) {
					output = output.substring(newlineIndex + 1);
				}
				return output;
			} catch (IOException x) {
				log.trace("IO EXCEPTION", x);
			}
			return null;
		}

	}

	// ======================================================================
	//
	// ITERATOR OVER ALL SUBSETS OF A SET
	//
	// ======================================================================

	/**
	 * Generic class to iterate over all subsets of a given set. Note that the empty
	 * set is never returned. The correct way to use this class is as follows:
	 * 
	 * <pre>
	 * Subsetter<X> z = new Subsetter<X>(...some set of X elements...);
	 * for (Set<X> s = new HashSet<X>(); s != null; s = z.advance()) {
	 *   ...do something with subset s...
	 * }
	 * </pre>
	 * 
	 * @param <T>
	 *            the base type of element
	 */
	private static class Subsetter<T> {

		/**
		 * A list version of the whole set. This is needed to access the individual
		 * elements by number.
		 */
		private List<T> list;

		/**
		 * The result set.
		 */
		private Set<T> set;

		/**
		 * The number of elements in the whole set.
		 */
		private int size;

		/**
		 * A bitset to record the elements of the whole set ({@link #list}) that are
		 * currently included in the result set ({@link #set}).
		 */
		private BitSet elements;

		/**
		 * Constructor for the subsetter. Class fields are initialized but no heavy
		 * computation is performed.
		 * 
		 * @param wholeSet
		 *                 the whole set over which subsets are taken
		 */
		Subsetter(Set<T> wholeSet) {
			list = new LinkedList<T>(wholeSet);
			set = new HashSet<T>();
			size = list.size();
			elements = new BitSet(size);
		}

		/**
		 * Calculates and returns the next subset. Once there are no more subsets, the
		 * method returns <code>null</code>.
		 * 
		 * @return the next subset of the whole set, or <code>null</code> if all subsets
		 *         have been returned
		 */
		public final Set<T> advance() {
			int i = 0;
			while ((i < size) && elements.get(i)) {
				set.remove(list.get(i));
				elements.clear(i++);
			}
			if (i == size) {
				return null;
			} else {
				set.add(list.get(i));
				elements.set(i);
				return set;
			}
		}

	}

}
