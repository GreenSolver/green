/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.util;

/**
 * Abstract base class for reporting mechanisms.
 */
public abstract class Reporter {

	/**
	 * The context in which we are reporting. This is usually changed by a specific
	 * context (a service or a store or some other component) before reporting
	 * starts.
	 */
	protected String context = "???";

	/**
	 * Set the context.
	 *
	 * @param context
	 *                new context
	 */
	public final void setContext(String context) {
		this.context = context;
	}

	/**
	 * Report an integer value within a given context.
	 *
	 * @param context
	 *                the context of the report
	 * @param key
	 *                report key
	 * @param value
	 *                integer report value
	 */
	public final void report(String context, String key, int value) {
		report(context, key, Integer.toString(value));
	}

	/**
	 * Report a long value within a given context.
	 *
	 * @param context
	 *                the context of the report
	 * @param key
	 *                report key
	 * @param value
	 *                long report value
	 */
	public final void report(String context, String key, long value) {
		report(context, key, Long.toString(value));
	}

	/**
	 * Report a double value within a given context.
	 *
	 * @param context
	 *                the context of the report
	 * @param key
	 *                report key
	 * @param value
	 *                double report value
	 */
	public final void report(String context, String key, double value) {
		report(context, key, Double.toString(value));
	}

	/**
	 * Report a string value within the current context.
	 *
	 * @param key
	 *              report key
	 * @param value
	 *              string report value
	 */
	public final void report(String key, String value) {
		report(context, key, value);
	}

	/**
	 * Report an integer value within the current context.
	 *
	 * @param key
	 *              report key
	 * @param value
	 *              integer report value
	 */
	public final void report(String key, int value) {
		report(context, key, Integer.toString(value));
	}

	/**
	 * Report a long value within the current context.
	 *
	 * @param key
	 *              report key
	 * @param value
	 *              long report value
	 */
	public final void report(String key, long value) {
		report(context, key, Long.toString(value));
	}

	/**
	 * Report a double value within the current context.
	 *
	 * @param key
	 *              report key
	 * @param value
	 *              double report value
	 */
	public final void report(String key, double value) {
		report(context, key, Double.toString(value));
	}

	/**
	 * Report a message within the current context.
	 *
	 * @param message
	 *                message to report
	 */
	public void reportMessage(String message) {
		reportMessage(context, message);
	}

	/**
	 * Abstract method that reports a given string message within a given context.
	 *
	 * @param context
	 *                context of the report
	 * @param message
	 *                message to report
	 */
	public abstract void reportMessage(String context, String message);

	/**
	 * Abstract method that reports a given string value within a given context.
	 *
	 * @param context
	 *                context of the report
	 * @param key
	 *                report key
	 * @param value
	 *                string report value
	 */
	public abstract void report(String context, String key, String value);

}
