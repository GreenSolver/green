/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.store;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;

import org.apache.logging.log4j.Logger;
import org.apfloat.Apint;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.util.Base64;

/**
 * Partial abstract implementation of a store.
 */
public abstract class BasicStore implements Store {

	/**
	 * Associated GREEN solver.
	 */
	protected final Green solver;

	/**
	 * Logging mechanism.
	 */
	protected final Logger log;

	/**
	 * Optional store name.
	 */
	protected String name;

	/**
	 * Create an instance of a basic store.
	 * 
	 * @param solver associated GREEN solver
	 */
	public BasicStore(final Green solver) {
		this.solver = solver;
		log = solver.getLogger();
	}

	public void setName(final String name) {
		this.name = name;
	}
	
	/**
	 * Do nothing.  Subclasses may override this method to remove stored information.
	 *
	 * @see za.ac.sun.cs.green.store.Store#clear()
	 */
	@Override
	public void clear() {		
	}

	/**
	 * Do nothing.  Subclasses may override this method to write stored information to underlying persistent storage.
	 *
	 * @see za.ac.sun.cs.green.store.Store#flushAll()
	 */
	@Override
	public void flushAll() {
	}

	/**
	 * Do nothing.  Subclasses are expected to override this method to clean up incomplete operations.
	 *
	 * @see za.ac.sun.cs.green.store.Store#shutdown()
	 */
	@Override
	public void shutdown() {
	}
	
	/**
	 * Read a base-64 encoded object from a string.
	 *
	 * @param string encoded source
	 * @return decoded object
	 * @throws IOException if the decoding is not a valid representation of an object
	 * @throws ClassNotFoundException if the object class cannot be located
	 */
	protected static Object fromString(String string) throws IOException, ClassNotFoundException {
		ObjectInputStream ois = new ObjectInputStream(new ByteArrayInputStream(Base64.decode(string)));
		Object o = ois.readObject();
		ois.close();
		return o;
	}

	/**
	 * Write an object as a base-64 encoded string.
	 *
	 * @param object object to encode
	 * @return encoded result
	 * @throws IOException if the encoded cannot be written to the string
	 */
	protected static String toString(Serializable object) throws IOException {
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		ObjectOutputStream oos = new ObjectOutputStream(baos);
		oos.writeObject(object);
		oos.close();
		return new String(Base64.encode(baos.toByteArray()));
	}

	@Override
	public String getString(String key) {
		Object value = get(key);
		return (value instanceof String) ? (String) value : null;
	}

	@Override
	public Boolean getBoolean(String key) {
		Object value = get(key);
		return (value instanceof Boolean) ? (Boolean) value : null;
	}

	@Override
	public Integer getInteger(String key) {
		Object value = get(key);
		return (value instanceof Integer) ? (Integer) value : null;
	}

	@Override
	public Long getLong(String key) {
		Object value = get(key);
		return (value instanceof Long) ? (Long) value : null;
	}

	@Override
	public Float getFloat(String key) {
		Object value = get(key);
		return (value instanceof Float) ? (Float) value : null;
	}

	@Override
	public Double getDouble(String key) {
		Object value = get(key);
		return (value instanceof Double) ? (Double) value : null;
	}

	@Override
	public Apint getApfloatInteger(String key) {
		Object value = get(key);
		return (value instanceof Apint) ? (Apint) value : null;
	}

}
