/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.util;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.HashSet;
import java.util.Properties;
import java.util.Set;

import org.apache.logging.log4j.Level;
import org.apache.logging.log4j.Logger;
import org.apache.logging.log4j.core.config.Configurator;

import za.ac.sun.cs.green.Service;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.store.Store;
import za.ac.sun.cs.green.taskmanager.TaskManager;

/**
 * Utility class that takes an instance of {@link Properties} and processes all
 * the "{@code green.service}" properties to configure a green solver.
 */
public class Configuration {

	/**
	 * The user's home directory.
	 */
	private static final String HOME_DIRECTORY = System.getProperty("user.home");

	/**
	 * The subdirectory in the user's home directory where the personal Green file
	 * is searched for.
	 */
	private static final String GREEN_DIRECTORY = ".green";

	/**
	 * The full name of the subdirectory where the personal file is searched for.
	 */
	private static final String HOME_GREEN_DIRECTORY = HOME_DIRECTORY + File.separator + GREEN_DIRECTORY
			+ File.separator;

	/**
	 * The Green solver to configure.
	 */
	private final Green solver;

	/**
	 * Logger.
	 */
	private final Logger log;

	/**
	 * The properties to use for the configuration.
	 */
	private final Properties properties;

	/**
	 * Whether default have been
	 */
	private boolean defaultsLoaded = false;

	/**
	 * Construct a configuration instance.
	 * 
	 * @param solver
	 *                   the Green solver to configure
	 * @param properties
	 *                   the properties to configure with
	 */
	public Configuration(final Green solver, final Properties properties) {
		this.solver = solver;
		log = solver.getLogger();
		this.properties = properties;
	}

	/**
	 * Add additional default properties to the set of properties of this
	 * configuration.
	 */
	private void loadDefaults() {
		if (defaultsLoaded) {
			return;
		}
		loadDefaults(log, properties);
		defaultsLoaded = true;
	}

	/**
	 * Add additional default properties to a set of properties. There are two
	 * places where such properties may be located:
	 * 
	 * <ol>
	 * <li>the file resource/build.properties</li>
	 * <li>the file $HOME/.green/build.properties</li>
	 * </ol>
	 * 
	 * The properties in these files are added to the {@link #properties} object if
	 * they are not already present there.
	 * 
	 * If the property name starts with "<code>$</code>", the property is added
	 * (after removing the "<code>$</code>") even if it already exists. In other
	 * words, this indicates that the property should be overwritten.
	 *
	 * @param log
	 *                   the logger
	 * @param properties
	 *                   the properties to which the defaults are added
	 */
	public static void loadDefaults(Logger log, Properties properties) {
		Properties homeProperties = loadPropertiesFromFile(log, HOME_GREEN_DIRECTORY + "green.properties");
		if (homeProperties == null) {
			homeProperties = loadPropertiesFromFile(log, HOME_GREEN_DIRECTORY + "build.properties");
		}
		loadDefaults(properties, homeProperties);
		Properties resourceProperties = loadPropertiesFromResource(log, "green.properties");
		if (resourceProperties == null) {
			resourceProperties = loadPropertiesFromResource(log, "build.properties");
		}
		loadDefaults(properties, resourceProperties);
	}

	/**
	 * Copy (some) properties to the official set of properties.
	 * 
	 * @param properties
	 *                      the target for new properties
	 * @param newProperties
	 *                      the source for new properties
	 */
	private static void loadDefaults(Properties properties, Properties newProperties) {
		if (newProperties != null) {
			for (Object k : newProperties.keySet()) {
				if (k instanceof String) {
					String key = (String) k;
					if (key.startsWith("$")) {
						properties.setProperty(key.substring(1), newProperties.getProperty(key));
					} else if (!properties.containsKey(key)) {
						properties.setProperty(key, newProperties.getProperty(key));
					}
				}
			}
		}
	}

	/**
	 * Load properties from a named file.
	 * 
	 * @param log
	 *                 the logger
	 * @param filename
	 *                 the name of the file
	 * @return the set of properties (or {@code null})
	 */
	public static Properties loadPropertiesFromFile(Logger log, String filename) {
		try {
			InputStream inputStream = new FileInputStream(filename);
			Properties properties = loadPropertiesFromStream(inputStream);
			log.trace("loaded configuration from {}", filename);
			return properties;
		} catch (FileNotFoundException e) {
			log.trace("failed to load configuration from {}", filename);
		} catch (IOException e) {
			log.trace("failed to load configuration from {}", filename);
		}
		return null;
	}

	/**
	 * Load properties from a named resource.
	 * 
	 * @param log
	 *                     the logger
	 * @param resourceName
	 *                     the name of the resource
	 * @return the set of properties (or {@code null})
	 */
	private static Properties loadPropertiesFromResource(Logger log, String resourceName) {
		final ClassLoader loader = Thread.currentThread().getContextClassLoader();
		try (InputStream resourceStream = loader.getResourceAsStream(resourceName)) {
			if (resourceStream != null) {
				return loadPropertiesFromStream(resourceStream);
			}
		} catch (IOException x) {
			log.trace("failed to load configuration from {}", resourceName);
		}
		return null;
	}

	/**
	 * Load properties from an input stream.
	 * 
	 * @param inputStream
	 *                    the input stream
	 * @return the set of properties
	 * @throws IOException
	 *                     if the input stream cannot be read
	 */
	private static Properties loadPropertiesFromStream(InputStream inputStream) throws IOException {
		Properties properties = new Properties();
		properties.load(inputStream);
		return properties;
	}

	/**
	 * Load properties from a string.
	 * 
	 * @param propertiesString
	 *                         the string with the properties
	 * @return the set of properties
	 */
	@SuppressWarnings("unused")
	private static Properties loadPropertiesFromString(String propertiesString) {
		if (propertiesString == null) {
			return null;
		}
		try {
			InputStream in = new ByteArrayInputStream(propertiesString.getBytes());
			return loadPropertiesFromStream(in);
		} catch (IOException x) {
			// ignore
		}
		return null;
	}

	/**
	 * Configure the Green solver by reading four important properties:
	 * {@code log.level}, {@code taskmanager}, {@code store}, and {@code services}.
	 * Based on the values of these properties, various routines are called in the
	 * Green instance.
	 * 
	 * @param loadDefaults
	 *                     whether or not default properties should be loaded
	 */
	public void configure(boolean loadDefaults) {
		if (loadDefaults) {
			loadDefaults();
		}
		String p = properties.getProperty("green.log.level");
		if (p != null) {
			Configurator.setLevel(log.getName(), Level.getLevel(p));
			log.info("green.log.level is deprecated -- IGNORED");
		}
		p = properties.getProperty("green.taskmanager");
		if (p != null) {
			TaskManager tm = (TaskManager) createInstance(p);
			if (tm != null) {
				solver.setTaskManager(tm);
			}
		}
		p = properties.getProperty("green.store");
		if (p != null) {
			Store st = (Store) createInstance(p);
			if (st != null) {
				solver.setStore(st);
			}
		}
		p = properties.getProperty("green.services");
		if (p != null) {
			for (String s : p.split(",")) {
				try {
					configure(s.trim());
				} catch (ParseException x) {
					log.fatal("parse error", x);
				}
			}
		}
		solver.setProperties(properties);
	}

	/**
	 * Load defaults and configure the Green solver.
	 */
	public void configure() {
		configure(true);
	}

	/**
	 * Used internally to register Green services.
	 * 
	 * @param serviceName
	 *                    the name of the service to register
	 * @throws ParseException
	 *                        if the properties contain badly-formatted service
	 *                        specifications
	 */
	private void configure(String serviceName) throws ParseException {
		String ss = properties.getProperty("green.service." + serviceName);
		if (ss != null) {
			ParseTree pt = new Parser(serviceName, ss).parse();
			for (ParseTree p : pt.getChildren()) {
				Service s = p.getService();
				solver.registerService(serviceName, s);
				configure(serviceName, s, p);
			}
		}
	}

	/**
	 * Used internally to register Green services. It recursively walks three the
	 * tree of service definitions.
	 * 
	 * @param rootName
	 *                  the name of the root service
	 * @param service
	 *                  the name of the subservice
	 * @param parseTree
	 *                  the tree of service definitions
	 */
	private void configure(String rootName, Service service, ParseTree parseTree) {
		for (ParseTree p : parseTree.getChildren()) {
			Service s = p.getService();
			solver.registerService(service, s);
			configure(rootName, s, p);
		}
	}

	/**
	 * Return the value of a property as an integer.
	 * 
	 * @param properties
	 *                     the properties to consult
	 * @param key
	 *                     the name of the property
	 * @param defaultValue
	 *                     the default value is the key is not found
	 * @return the integer value
	 */
	public static int getIntegerProperty(Properties properties, String key, int defaultValue) {
		String s = properties.getProperty(key, Integer.toString(defaultValue));
		try {
			return Integer.parseInt(s);
		} catch (NumberFormatException x) {
			// Ignore
		}
		return defaultValue;
	}

	/**
	 * Create an instance of a given class.
	 * 
	 * @param objectName
	 *                   the name of the class
	 * @return the new instance
	 */
	private Object createInstance(String objectName) {
		Class<?> classx = loadClass(objectName);
		try {
			Constructor<?> constructor = null;
			try {
				constructor = classx.getConstructor(Green.class);
				return constructor.newInstance(solver);
			} catch (NoSuchMethodException x) {
				// ignore
			}
			try {
				constructor = classx.getConstructor(Green.class, Properties.class);
				return constructor.newInstance(solver, properties);
			} catch (NoSuchMethodException x) {
				log.fatal("constructor not found: " + objectName, x);
			}
		} catch (SecurityException x) {
			log.fatal("constructor not found: " + objectName, x);
		} catch (IllegalArgumentException x) {
			log.fatal("constructor error: " + objectName, x);
		} catch (InstantiationException x) {
			log.fatal("constructor error: " + objectName, x);
		} catch (IllegalAccessException x) {
			log.fatal("constructor error: " + objectName, x);
		} catch (InvocationTargetException x) {
			log.fatal("constructor error: " + objectName, x);
		}
		return null;
	}

	/**
	 * Load a given class.
	 * 
	 * @param className
	 *                  the class to load
	 * @return the loaded class or {@code null} if something went wrong
	 */
	private Class<?> loadClass(String className) {
		final ClassLoader loader = Thread.currentThread().getContextClassLoader();
		if ((className != null) && (className.length() > 0)) {
			try {
				return loader.loadClass(className);
			} catch (ClassNotFoundException x) {
				log.fatal("class not found: " + className, x);
			} catch (ExceptionInInitializerError x) {
				log.fatal("class not found: " + className, x);
			}
		}
		return null;
	}

	// ======================================================================
	//
	// SERVICE TREE
	//
	// ======================================================================

	/**
	 * GREEN service tree.
	 */
	private class ParseTree {

		/**
		 * The service stored in this node.
		 */
		private final Service service;

		/**
		 * The child services for this node,
		 */
		private final Set<ParseTree> children;

		/**
		 * Construct a node in the service parse tree.
		 * 
		 * @param service
		 *                service for the node
		 */
		ParseTree(final Service service) {
			this.service = service;
			children = new HashSet<Configuration.ParseTree>();
		}

		/**
		 * Add a child service to this node.
		 *
		 * @param child
		 *              child service
		 */
		public void addChild(ParseTree child) {
			children.add(child);
		}

		/**
		 * Return the child service of this node as a set.
		 *
		 * @return set of child services
		 */
		public Set<ParseTree> getChildren() {
			return children;
		}

		/**
		 * Return the service stored in this node.
		 *
		 * @return node service
		 */
		public Service getService() {
			return service;
		}

	}

	// ======================================================================
	//
	// EXCEPTION FOR SERVICE LANGUAGE
	//
	// ======================================================================

	/**
	 * An exception that represents a parse error that occurred while reading the
	 * specification of a GREEN service.
	 */
	private class ParseException extends Exception {

		/**
		 * Required for serialization.
		 */
		private static final long serialVersionUID = 7249730234672500827L;

		/**
		 * Construct a new parse exception.
		 * 
		 * @param string
		 *               exception message
		 */
		ParseException(String string) {
			super(string);
		}

	}

	// ======================================================================
	//
	// PARSER FOR SERVICE LANGUAGE
	//
	// ======================================================================

	/**
	 * Parser for the specification of GREEN services.
	 */
	private class Parser {

		/**
		 * Name of the overall service.
		 */
		private final String rootName;

		/**
		 * Scanner for tokens of service.
		 */
		private final Scanner scanner;

		/**
		 * Create a service parser with the given service name and given input string.
		 * 
		 * @param rootName
		 *                 name of the service
		 * @param input
		 *                 input string for the parser
		 * @throws ParseException
		 *                        when a parse error occurs
		 */
		Parser(final String rootName, final String input) throws ParseException {
			this.rootName = rootName;
			scanner = new Scanner(input);
		}

		/**
		 * Initiate parsing and return the resulting service tree.
		 *
		 * @return the service parse tree that results from parsing the input string
		 * @throws ParseException
		 *                        when a parse error occurs
		 */
		public ParseTree parse() throws ParseException {
			return parse(null);
		}

		/**
		 * Internal routine to recursively parse a service definition.
		 *
		 * @param service
		 *                service at the root of the parse tree
		 * @return service parse tree
		 * @throws ParseException
		 *                        when a parse error occurs
		 */
		private ParseTree parse(Service service) throws ParseException {
			ParseTree t = new ParseTree(service);
			while ((scanner.next() != Token.EOS) && (scanner.next() != Token.RPAREN)) {
				if (scanner.next() == Token.NAME) {
					String n = scanner.expectName();
					Service s = lookup(rootName, n);
					if (s == null) {
						throw new ParseException("Unknown service \"" + rootName + "." + n + "\"");
					}
					t.addChild(new ParseTree(s));
				} else if (scanner.next() == Token.LPAREN) {
					scanner.scan(); // '('
					String n = scanner.expectName();
					Service s = lookup(rootName, n);
					if (s == null) {
						throw new ParseException("Unknown service \"" + rootName + "." + n + "\"");
					}
					t.addChild(parse(s));
					scanner.expect(Token.RPAREN); // ')'
				} else {
					throw new ParseException("Unexpected token in \"" + scanner.getInput() + "\"");
				}
			}
			return t;
		}

		/**
		 * Look up an instance of a service given its name and the name of the root
		 * service.
		 *
		 * @param rootName
		 *                    name of root service
		 * @param serviceName
		 *                    name of particular service
		 * @return instance of particular service
		 */
		private Service lookup(String rootName, String serviceName) {
			String s = properties.getProperty("green.service." + rootName + "." + serviceName);
			if (s != null) {
				return (Service) createInstance(s);
			}
			return null;
		}

	}

	// ======================================================================
	//
	// TOKENS FOR SERVICE LANGUAGE
	//
	// ======================================================================

	/**
	 * Tokens used for parsing service specifications.
	 */
	public enum Token {
		// @formatter:off
		LPAREN("\"(\""),
		RPAREN("\")\""),
		NAME("a name"),
		EOS("the end of input"),
		UNKNOWN("an unknown token");
		// @formatter:on

		/**
		 * A string representation of the token.
		 */
		private final String representation;

		/**
		 * Construct a new token.
		 * 
		 * @param representation
		 *                       a string representation of the token
		 */
		private Token(String representation) {
			this.representation = representation;
		}

		/**
		 * Return the string representation of the token.
		 *
		 * @return token's string representation
		 *
		 * @see java.lang.Enum#toString()
		 */
		@Override
		public String toString() {
			return representation;
		}

	}

	// ======================================================================
	//
	// SCANNER FOR SERVICE LANGUAGE
	//
	// ======================================================================

	/**
	 * Scanner for the specification of GREEN services.
	 */
	private class Scanner {

		/**
		 * Input string to parse.
		 */
		private final String input;

		/**
		 * Position of next character to parse in input string.
		 */
		private int position;

		/**
		 * Identity of most recently scanned token.
		 */
		private Token nextToken;

		/**
		 * Next character to scan.
		 */
		private char nextChar;

		/**
		 * Most recently scanned name (when {@linkplain #nextToken} is
		 * {@linkplain Token#NAME}).
		 */
		private String nextName;

		/**
		 * Create a new scanner that will scan the given input string.
		 * 
		 * @param input
		 *              string to scan
		 * @throws ParseException
		 *                        when a parse error occurs
		 */
		Scanner(final String input) throws ParseException {
			this.input = input;
			position = 0;
			nextToken = Token.UNKNOWN;
			nextChar = ' ';
			nextName = "";
			scan();
		}

		/**
		 * Return the original input string.
		 *
		 * @return original input
		 */
		public String getInput() {
			return input;
		}

		/**
		 * Check that the next token is the same as the given parameter, and scan past
		 * it.
		 *
		 * @param token
		 *              expected token
		 * @throws ParseException
		 *                        if the next token in the input is not as expected
		 */
		public void expect(Token token) throws ParseException {
			if (nextToken != token) {
				throw new ParseException("Expected " + token + " but found " + nextToken + " in \"" + input + "\"");
			}
			scan();
		}

		/**
		 * Check that the next token is a name and return it.
		 *
		 * @return the name that appears next in the input
		 * @throws ParseException
		 *                        if the next token in the input is not a name
		 */
		public String expectName() throws ParseException {
			String n = nextName;
			expect(Token.NAME);
			return n;
		}

		/**
		 * Return the next token.
		 *
		 * @return next token in the input
		 */
		public Token next() {
			return nextToken;
		}

		/**
		 * Scan the next token.
		 *
		 * @throws ParseException
		 *                        if an unrecognized token is encountered
		 */
		private void scan() throws ParseException {
			nextToken = Token.UNKNOWN;
			while (nextToken == Token.UNKNOWN) {
				if (nextChar == '\0') {
					nextToken = Token.EOS;
				} else if (Character.isWhitespace(nextChar)) {
					readNext();
				} else if (nextChar == '(') {
					nextToken = Token.LPAREN;
					readNext();
				} else if (nextChar == ')') {
					nextToken = Token.RPAREN;
					readNext();
				} else if (Character.isLetter(nextChar)) {
					StringBuilder n = new StringBuilder();
					while (Character.isLetterOrDigit(nextChar)) {
						n.append(nextChar);
						readNext();
					}
					nextName = n.toString();
					nextToken = Token.NAME;
				} else {
					throw new ParseException("Unrecognized token in \"" + input + "\"");
				}
			}
		}

		/**
		 * Read the next character.
		 */
		private void readNext() {
			if (position == input.length()) {
				nextChar = '\0';
			} else {
				nextChar = input.charAt(position++);
			}
		}

	}

}
