/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.store;

import java.io.Serializable;
import java.util.Set;

import org.apfloat.Apfloat;
import org.apfloat.Apint;

import za.ac.sun.cs.green.util.Reporter;

/**
 * An interface to a data store that can record various kinds of objects.
 */
public interface Store {

	/**
	 * Set a name for this store. This will be called for all stores; in some cases
	 * the name may be {@code null} if the store is unnamed.
	 *
	 * @param name
	 *             name for this store
	 */
	void setName(final String name);

	/**
	 * Shuts down the store. For example, in the case of an SQL database, this
	 * routine might close the connection.
	 */
	void shutdown();

	/**
	 * Shuts down the store. For example, in the case of an SQL database, this
	 * routine might close the connection.
	 */
	void report(Reporter reporter);

	/**
	 * Returns an arbitrary object that is associated with the given key. If there
	 * is nothing associated with the key, the method returns {@code null}.
	 * 
	 * @param key
	 *            the key to use for the lookup
	 * @return the object that is stored with the key or {@code null} if no
	 *         association is found
	 */
	Object get(String key);

	/**
	 * Returns the string that is associated with the given key. If there is nothing
	 * associated with the key, the method returns {@code null}.
	 * 
	 * @param key
	 *            the key to use for the lookup
	 * @return the string that is stored with the key or {@code null} if no
	 *         association is found
	 */
	String getString(String key);

	/**
	 * Returns the {@code boolean} that is associated with the given key. If there
	 * is nothing associated with the key, the method returns {@code null}.
	 * 
	 * @param key
	 *            the key to use for the lookup
	 * @return the {@code boolean} that is stored with the key or {@code null} if no
	 *         association is found
	 */
	Boolean getBoolean(String key);

	/**
	 * Returns the integer that is associated with the given key. If there is
	 * nothing associated with the key, the method returns {@code null}.
	 * 
	 * @param key
	 *            the key to use for the lookup
	 * @return the integer that is stored with the key or {@code null} if no
	 *         association is found
	 */
	Integer getInteger(String key);

	/**
	 * Returns the {@code long} value that is associated with the given key. If
	 * there is nothing associated with the key, the method returns {@code null}.
	 * 
	 * @param key
	 *            the key to use for the lookup
	 * @return the {@code long} value that is stored with the key or {@code null} if
	 *         no association is found
	 */
	Long getLong(String key);

	/**
	 * Returns the {@code float} value that is associated with the given key. If
	 * there is nothing associated with the key, the method returns {@code null}.
	 * 
	 * @param key
	 *            the key to use for the lookup
	 * @return the {@code float} value that is stored with the key or {@code null}
	 *         if no association is found
	 */
	Float getFloat(String key);

	/**
	 * Returns the {@code double} value that is associated with the given key. If
	 * there is nothing associated with the key, the method returns {@code null}.
	 * 
	 * @param key
	 *            the key to use for the lookup
	 * @return the {@code double} value that is stored with the key or {@code null}
	 *         if no association is found
	 */
	Double getDouble(String key);

	/**
	 * Returns the {@link Apfloat} integer that is associated with the given key. If
	 * there is nothing associated with the key, the method returns {@code null}.
	 * 
	 * @param key
	 *            the key to use for the lookup
	 * @return the integer that is stored with the key or {@code null} if no
	 *         association is found
	 */
	Apint getApfloatInteger(String key);

	/**
	 * Associates the given serializable value with the given key.
	 * 
	 * @param key
	 *              the key for the association
	 * @param value
	 *              the serializable value for the association
	 */
	void put(String key, Serializable value);

	/**
	 * Optionally flush all stored information to underlying persistent storage.
	 */
	void flushAll();

	/**
	 * Clear the cache.
	 */
	void clear();

	/**
	 * Returns the key of all entries in the cache
	 * 
	 * @return Set of keys
	 */
	Set<String> keySet();

}
