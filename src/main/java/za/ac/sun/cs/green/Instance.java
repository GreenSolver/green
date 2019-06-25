package za.ac.sun.cs.green;

import java.util.Hashtable;
import java.util.Map;

import org.apache.logging.log4j.Logger;

import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;

/**
 * An instance of a problem that Green will be asked to solve. Each instance
 * involves an expression (to solve), but also additional information such as a
 * parent instance (that may contain additional expressions that is combined
 * with the instance expression) and satellite data (that services can set to
 * aid with the solution.
 * 
 * @author Jaco Geldenhuys <jaco@cs.sun.ac.za>
 */
public class Instance {

	/**
	 * The Green solver to which this instance belongs.
	 */
	protected final Green solver;

	/**
	 * The logger of the solver.
	 */
	protected final Logger log;

	/**
	 * If this instance is generated on-the-fly to help solve another instance, this
	 * fields stores the originating instance.
	 */
	protected Instance source;

	/**
	 * Another instance that can be assumed to be solved and that is combined with
	 * this instance.
	 */
	protected final Instance parent;

	/**
	 * The expression to solve.
	 */
	protected final Expression expression;

	/**
	 * The combination of this instance's expression and that of its parent.
	 */
	protected Expression fullExpression;

	/**
	 * Satellite data.
	 */
	protected final Map<Object, Object> data;

	/**
	 * Create an instance of a problem to solve. Since the source is not explicitly
	 * set, it is set to the source of the parent, if not {@code null}. If the
	 * parent is {@code null}, the source is set to {@code null}. In all cases, the
	 * source will be changed to this instance itself when a service is requested.
	 * 
	 * @param solver     the solver that must solve the instance
	 * @param parent     associated parent instance
	 * @param expression the expression
	 */
	public Instance(final Green solver, final Instance parent, final Expression expression) {
		this.solver = solver;
		this.log = solver.getLogger();
		this.source = (parent == null) ? null : parent.source;
		this.parent = parent;
		this.expression = expression;
		fullExpression = null;
		data = new Hashtable<Object, Object>();
	}

	/**
	 * Create an instance of a problem to solve.
	 * 
	 * @param solver     the solver that must solve the instance
	 * @param source     the source instance that spawned this instance
	 * @param parent     associated parent instance
	 * @param expression the expression
	 */
	public Instance(final Green solver, final Instance source, final Instance parent, final Expression expression) {
		this.solver = solver;
		this.log = solver.getLogger();
		this.source = source;
		this.parent = parent;
		this.expression = expression;
		fullExpression = null;
		data = new Hashtable<Object, Object>();
	}

	/**
	 * Return the source of this instance. If no explicit source was set when the
	 * instance was created, the parent is used as a source. It might be
	 * {@code null}.
	 * 
	 * @return source of this instance
	 */
	public Instance getSource() {
		return source;
	}

	/**
	 * Return the parent of this instance.
	 * 
	 * @return parent of this instance
	 */
	public Instance getParent() {
		return parent;
	}

	/**
	 * Return the expression of this instance.
	 * 
	 * @return expression of this instance
	 */
	public Expression getExpression() {
		return expression;
	}

	/**
	 * Return the full expression of this instance: it is the conjunction of the
	 * instance's expression and that of the parent, if not {@code null}.
	 * 
	 * @return full expression for this instance
	 */
	public Expression getFullExpression() {
		if (fullExpression == null) {
			Instance p = getParent();
			Expression e = (p == null) ? null : p.getFullExpression();
			fullExpression = (e == null) ? expression : new Operation(Operation.Operator.AND, expression, e);
		}
		return fullExpression;
	}

	/**
	 * Request that the solver apply a defined service to this instance
	 * 
	 * @param serviceName the name of the defined service
	 * @return the result of the service
	 */
	public Object request(String serviceName) {
		log.info("[{}] request \"{}\"", this, serviceName);
		source = this;
		Object result = solver.handleRequest(serviceName, this);
		log.info("[{}] request result: {}", this, result);
		return result;
	}

	/**
	 * Set satellite data for this instance.
	 * 
	 * @param key   the key for the data
	 * @param value the value for the data
	 */
	public void setData(Object key, Object value) {
		log.trace("[{}] set satellite [{}] -> [{}]", this, key, value);
		data.put(key, value);
	}

	/**
	 * Retrieve satellite data for this instance.
	 * 
	 * @param key the key for the data
	 * @return the value of the data
	 */
	public Object getData(Object key) {
		return data.get(key);
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		if (expression == null) {
			return 0;
		} else {
			return expression.hashCode();
		}
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (!(obj instanceof Instance)) {
			return false;
		} else {
			Instance i = (Instance) obj;
			Expression e1 = getExpression();
			Expression e2 = i.getExpression();
			if ((e1 == null) || (e2 == null)) {
				return false;
			} else {
				return e1.equals(e2);
			}
		}
	}

}
