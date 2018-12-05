package za.ac.sun.cs.green.util;

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
 * This is a utility class that takes an instance of {@link Properties} and
 * processes all the "{@code green.service}" properties to configure a green
 * solver.
 * 
 * @author jaco
 */
public class Configuration {

	private final Green solver;

	private final Logger LOGGER;

	private final Properties properties;

	private final ClassLoader loader = Configuration.class.getClassLoader();

	public Configuration(final Green solver, final Properties properties) {
		this.solver = solver;
		LOGGER = solver.getLogger();
		this.properties = properties;
	}

	public void configure() {
		String p = properties.getProperty("green.log.level");
		if (p != null) {
			Configurator.setLevel(LOGGER.getName(), Level.getLevel(p));
			// setLevel(Level.getLevel(p));
			LOGGER.trace("logging level changed to {}", p);
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
					LOGGER.fatal("parse error", x);
				}
			}
		}
	}

//	private void setLevel(Level level) {
//		final LoggerContext ctx = (LoggerContext) LogManager.getContext(false);
//		final org.apache.logging.log4j.core.config.Configuration config = ctx.getConfiguration();
//		LoggerConfig loggerConfig = config.getLoggerConfig(LOGGER.getName());
//		LoggerConfig specificConfig = loggerConfig;
//		if (!loggerConfig.getName().equals(LOGGER.getName())) {
//			specificConfig = new LoggerConfig(LOGGER.getName(), level, true);
//			specificConfig.setParent(loggerConfig);
//			config.addLogger(LOGGER.getName(), specificConfig);
//		}
//		specificConfig.setLevel(level);
//		ctx.updateLoggers();
//	}

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

	private void configure(String rootName, Service service, ParseTree parseTree) {
		for (ParseTree p : parseTree.getChildren()) {
			Service s = p.getService();
			solver.registerService(service, s);
			configure(rootName, s, p);
		}
	}

	public static int getIntegerProperty(Properties properties, String key, int defaultValue) {
		String s = properties.getProperty(key, Integer.toString(defaultValue));
		try {
			return Integer.parseInt(s);
		} catch (NumberFormatException x) {
			// Ignore
		}
		return defaultValue;
	}

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
				constructor = classx.getConstructor(Green.class,
						Properties.class);
				return constructor.newInstance(solver, properties);
			} catch (NoSuchMethodException x) {
				LOGGER.fatal("constructor not found: " + objectName, x);
			}
		} catch (SecurityException x) {
			LOGGER.fatal("constructor not found: " + objectName, x);
		} catch (IllegalArgumentException x) {
			LOGGER.fatal("constructor error: " + objectName, x);
		} catch (InstantiationException x) {
			LOGGER.fatal("constructor error: " + objectName, x);
		} catch (IllegalAccessException x) {
			LOGGER.fatal("constructor error: " + objectName, x);
		} catch (InvocationTargetException x) {
			LOGGER.fatal("constructor error: " + objectName, x);
		}
		return null;
	}

	private Class<?> loadClass(String className) {
		if ((className != null) && (className.length() > 0)) {
			try {
				return loader.loadClass(className);
			} catch (ClassNotFoundException x) {
				LOGGER.fatal("class not found: " + className, x);
			} catch (ExceptionInInitializerError x) {
				LOGGER.fatal("class not found: " + className, x);
			}
		}
		return null;
	}

	private class ParseTree {

		private final Service service;

		private final Set<ParseTree> children;

		public ParseTree(final Service service) {
			this.service = service;
			children = new HashSet<Configuration.ParseTree>();
		}

		public void addChild(ParseTree child) {
			children.add(child);
		}

		public Set<ParseTree> getChildren() {
			return children;
		}

		public Service getService() {
			return service;
		}

	}

	@SuppressWarnings("serial")
	private class ParseException extends Exception {

		public ParseException(String string) {
			super(string);
		}

	}

	private class Parser {

		private final String rootName;

		private final Scanner scanner;

		public Parser(final String rootName, final String input)
				throws ParseException {
			this.rootName = rootName;
			scanner = new Scanner(input);
		}

		public ParseTree parse() throws ParseException {
			return parse(null);
		}

		public ParseTree parse(Service service) throws ParseException {
			ParseTree t = new ParseTree(service);
			while ((scanner.next() != Token.EOS)
					&& (scanner.next() != Token.RPAREN)) {
				if (scanner.next() == Token.NAME) {
					String n = scanner.expectName();
					Service s = lookup(rootName, n);
					if (s == null) {
						throw new ParseException("Unknown service \""
								+ rootName + "." + n + "\"");
					}
					t.addChild(new ParseTree(s));
				} else if (scanner.next() == Token.LPAREN) {
					scanner.scan(); // '('
					String n = scanner.expectName();
					Service s = lookup(rootName, n);
					if (s == null) {
						throw new ParseException("Unknown service \""
								+ rootName + "." + n + "\"");
					}
					t.addChild(parse(s));
					scanner.expect(Token.RPAREN); // ')'
				} else {
					throw new ParseException("Unexpected token in \""
							+ scanner.getInput() + "\"");
				}
			}
			return t;
		}

		private Service lookup(String rootName, String serviceName) {
			String s = properties.getProperty("green.service." + rootName + "."
					+ serviceName);
			if (s != null) {
				return (Service) createInstance(s);
			}
			return null;
		}

	}

	public enum Token {
		LPAREN("\"(\""), RPAREN("\")\""), NAME("a name"), EOS(
				"the end of input"), UNKNOWN("an unknown token");

		private final String representation;

		private Token(String representation) {
			this.representation = representation;
		}

		@Override
		public String toString() {
			return representation;
		}

	}

	private class Scanner {

		private final String input;

		private int position;

		private Token nextToken;

		private char nextChar;

		private String nextName;

		public Scanner(final String input) throws ParseException {
			this.input = input;
			position = 0;
			nextToken = Token.UNKNOWN;
			nextChar = ' ';
			nextName = "";
			scan();
		}

		public String getInput() {
			return input;
		}

		public void expect(Token token) throws ParseException {
			if (nextToken != token) {
				throw new ParseException("Expected " + token + " but found "
						+ nextToken + " in \"" + input + "\"");
			}
			scan();
		}

		public String expectName() throws ParseException {
			String n = nextName;
			expect(Token.NAME);
			return n;
		}

		public Token next() {
			return nextToken;
		}

		public void scan() throws ParseException {
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
					throw new ParseException("Unrecognized token in \"" + input
							+ "\"");
				}
			}
		}

		public void readNext() {
			if (position == input.length()) {
				nextChar = '\0';
			} else {
				nextChar = input.charAt(position++);
			}
		}

	}
}
