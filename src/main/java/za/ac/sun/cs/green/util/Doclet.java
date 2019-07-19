/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */
package za.ac.sun.cs.green.util;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.io.Writer;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.SortedSet;
import java.util.StringTokenizer;
import java.util.TreeSet;

import com.sun.javadoc.ClassDoc;
import com.sun.javadoc.ConstructorDoc;
import com.sun.javadoc.Doc;
import com.sun.javadoc.DocErrorReporter;
import com.sun.javadoc.ExecutableMemberDoc;
import com.sun.javadoc.FieldDoc;
import com.sun.javadoc.LanguageVersion;
import com.sun.javadoc.MethodDoc;
import com.sun.javadoc.PackageDoc;
import com.sun.javadoc.ParamTag;
import com.sun.javadoc.Parameter;
import com.sun.javadoc.RootDoc;
import com.sun.javadoc.Tag;

/**
 * Custom Javadoc class for generating the API for the official documentation.
 */
public class Doclet {

	/**
	 * Single instance of this class.
	 */
	private static Doclet doclet;

	/**
	 * Return the singleton doclet.
	 *
	 * @return singleton doclet
	 */
	private static Doclet getDoclet() {
		if (doclet == null) {
			doclet = new Doclet();
		}
		return doclet;
	}

	/**
	 * Initiate the generation of documentation.
	 *
	 * @param root
	 *             root of the program structure information
	 * @return {@code true} if and only if generation was successful
	 */
	public static boolean start(RootDoc root) {
		return getDoclet().startDoc(root);
	}

	/**
	 * Return the number of arguments on the command line for the given option. This
	 * includes the option itself. For example, "{@code -t MyTitle}" should return
	 * 2.
	 *
	 * @param option
	 *               particular option
	 * @return number of option arguments (including option itself)
	 */
	public static int optionLength(String option) {
		return getDoclet().getOptionLength(option);
	}

	/**
	 * Check that options have the correct arguments.
	 *
	 * @param options
	 *                 array of options to check
	 * @param reporter
	 *                 mechanism for reporting errors
	 * @return {@code true} if and only if the options are valid
	 */
	public static boolean validOptions(String[][] options, DocErrorReporter reporter) {
		return getDoclet().areValidOptions(options, reporter);
	}

	/**
	 * Return the version of the Java Programming Language supported by this doclet.
	 *
	 * @return the language version supported by this doclet
	 */
	public static LanguageVersion languageVersion() {
		return getDoclet().getLanguageVersion();
	}

	// ======================================================================
	//
	// DOCLET CLASS
	//
	// ======================================================================

	/**
	 * Name of directory where documentation is generated.
	 */
	private String destination = ".";

	/**
	 * Prefixes of packages for which no documentation is generated.
	 */
	private final Set<String> excludedQualifiers = new HashSet<>();

	/**
	 * Array of packages for which documentation is generated.
	 */
	private PackageDoc[] greenPackages;

	/**
	 * Array of classes for which documentation is generated.
	 */
	private final Set<ClassDoc> greenClasses = new HashSet<>();

	/**
	 * Initiate the generation of documentation.
	 *
	 * @param root
	 *             root of the program structure information
	 * @return {@code true} if and only if generation was successful
	 */
	private boolean startDoc(RootDoc root) {
		try {
			setOptions(root.options());
			initArrays(root);
			generatePackageSummary();
		} catch (IOException e) {
			root.printError(e.getMessage());
			return false;
		}
		root.printNotice("Done");
		return true;
	}

	/**
	 * Return the number of arguments on the command line for the given option. This
	 * includes the option itself. For example, "{@code -t MyTitle}" should return
	 * 2.
	 *
	 * @param option
	 *               particular option
	 * @return number of option arguments (including option itself)
	 */
	private int getOptionLength(String option) {
		option = option.toLowerCase();
		if (option.equals("-author") || option.equals("-docfilessubdirs") || option.equals("-javafx")
				|| option.equals("-keywords") || option.equals("-linksource") || option.equals("-nocomment")
				|| option.equals("-nodeprecated") || option.equals("-nodeprecatedlist") || option.equals("-nohelp")
				|| option.equals("-noindex") || option.equals("-nonavbar") || option.equals("-nosince")
				|| option.equals("-notimestamp") || option.equals("-notree") || option.equals("-quiet")
				|| option.equals("-serialwarn") || option.equals("-splitindex") || option.equals("-use")
				|| option.equals("-version") || option.equals("-xnodate")) {
			return 1;
		} else if (option.equals("-charset") || option.equals("-bottom") || option.equals("-d")
				|| option.equals("-docencoding") || option.equals("-doctitle") || option.equals("-encoding")
				|| option.equals("-excludedocfilessubdir") || option.equals("-footer") || option.equals("-header")
				|| option.equals("-helpfile") || option.equals("-link") || option.equals("-noqualifier")
				|| option.equals("-output") || option.equals("-sourcepath") || option.equals("-sourcetab")
				|| option.equals("-stylesheetfile") || option.equals("-tag") || option.equals("-taglet")
				|| option.equals("-tagletpath") || option.equals("-top") || option.equals("-windowtitle")
				|| option.equals("-xprofilespath")) {
			return 2;
		} else if (option.equals("-group") || option.equals("-linkoffline")) {
			return 3;
		} else {
			return -1; // indicate we don't know about it
		}
	}

	/**
	 * Check that options have the correct arguments.
	 *
	 * @param options
	 *                 array of options to check
	 * @param reporter
	 *                 mechanism for reporting errors
	 * @return {@code true} if and only if the options are valid
	 */
	private boolean areValidOptions(String[][] options, DocErrorReporter reporter) {
		return true;
	}

	/**
	 * Return the version of the Java Programming Language supported by this doclet.
	 *
	 * @return the language version supported by this doclet
	 */
	private LanguageVersion getLanguageVersion() {
		return LanguageVersion.JAVA_1_5;
	}

	/**
	 * Process the given options.
	 *
	 * @param options
	 *                options to process
	 */
	private void setOptions(String[][] options) {
		for (int i = 0, n = options.length; i < n; i++) {
			String option = options[i][0];
			if (option.equals("-d")) {
				destination = options[i][1];
				new File(destination).mkdirs();
			} else if (option.equals("-noqualifier")) {
				addToSet(excludedQualifiers, options[i][1]);
			}
		}
	}

	/**
	 * Add the ":"-separated substrings of the second parameter to a set.
	 *
	 * @param set
	 *            the set to add to
	 * @param str
	 *            the string to add
	 */
	private void addToSet(Set<String> set, String str) {
		StringTokenizer st = new StringTokenizer(str, ":");
		String current;
		while (st.hasMoreTokens()) {
			current = st.nextToken();
			set.add(current);
		}
	}

	/**
	 * Remove the prefix of a qualified Java class if the prefix appears in the list
	 * of excluded qualifiers.
	 *
	 * @param qualified
	 *                  Java class to process
	 * @return qualified Java class with prefix removed if necessary
	 */
	private String excludeQualifier(String qualifier) {
		for (String excludedQualifier : excludedQualifiers) {
			if (excludedQualifier.endsWith("*")) {
				if (qualifier.startsWith(excludedQualifier.substring(0, excludedQualifier.length() - 1))) {
					int index = qualifier.lastIndexOf(".", qualifier.length() + 1 - 1);
					return qualifier.substring(index + 1);
				}
			}
		}
		int index = qualifier.length() + 1;
		while ((index = qualifier.lastIndexOf(".", index - 1)) != -1) {
			String prefix = qualifier.substring(0, index + 1);
			if (excludedQualifiers.contains(prefix)) {
				return qualifier.substring(index + 1);
			}
		}
		return qualifier;
	}

	/**
	 * Extract the list of packages to generate documentation for.
	 *
	 * @param root
	 *             documentation information for all referenced source files
	 */
	private void initArrays(RootDoc root) {
		Set<PackageDoc> greenSet = new HashSet<>();
		for (ClassDoc classDoc : root.classes()) {
			PackageDoc packag = classDoc.containingPackage();
			if (packag.name().startsWith("za.ac.sun.cs.green")) {
				greenSet.add(packag);
				greenClasses.add(classDoc);
			}
		}
		greenPackages = sortList(greenSet);
	}

	/**
	 * Generate an overview (in essence, a list) of all documented packages.
	 *
	 * @throws IOException
	 *                     if some I/O error occurred
	 */
	private void generatePackageSummary() throws IOException {
		MdWriter writer = new MdWriter(destination, "GREEN", false);
		writer.section("sidebar").sectionEnd();
		writer.section("main").h1("{{ page.title | escape }}");
		writer.table("packages").thead().tr();
		writer.th().cdata("Package").thEnd();
		writer.th().cdata("Description").thEnd();
		writer.trEnd().theadEnd().tbody();
		for (PackageDoc packageDoc : greenPackages) {
			writer.tr();
			writer.td().a(packageDoc.name(), packageDoc.name()).tdEnd();
			writer.td().tags(packageDoc.firstSentenceTags()).tdEnd();
			writer.trEnd();
			generatePackage(packageDoc);
		}
		writer.tbodyEnd().tableEnd();
		writer.sectionEnd();
		writer.close();
	}

	/**
	 * Generate documentation for the given package.
	 *
	 * @param packageDoc
	 *                   package to document
	 * @throws IOException
	 *                     if some I/O error occurred
	 */
	private void generatePackage(PackageDoc packageDoc) throws IOException {
		MdWriter writer = new MdWriter(destination, packageDoc.name(), packageDoc.name());
		generatePackageSidebar(writer);
		writer.section("main package").h1("{{ page.title | escape }}");
		writer.tags(packageDoc.inlineTags(), -1);
		int interfaceCount = 0;
		ClassDoc[] interfaces = sortList(packageDoc.interfaces());
		if (interfaces.length > 0) {
			writer.h2("Interfaces").table("classes").tbody();
			for (ClassDoc interfac : interfaces) {
				writer.tr();
				writer.td().a(interfac.name(), interfac.name()).tdEnd();
				writer.td().tags(interfac.firstSentenceTags()).tdEnd();
				writer.trEnd();
				generateClass(interfac);
				interfaceCount++;
			}
			writer.tbodyEnd().tableEnd();
		}
		if (interfaceCount > 0) {
			ClassDoc[] classes = sortList(packageDoc.allClasses());
			writer.h2("Classes").table("classes").tbody();
			for (ClassDoc classDoc : classes) {
				if (classDoc.isInterface()) {
					continue;
				}
				writer.tr();
				writer.td().a(classDoc.name(), classDoc.name()).tdEnd();
				writer.td().tags(classDoc.firstSentenceTags()).tdEnd();
				writer.trEnd();
				generateClass(classDoc);
			}
			writer.tbodyEnd().tableEnd();
		}
		if (hasAfterTag(packageDoc.inlineTags())) {
			writer.h2("Description").tags(packageDoc.inlineTags(), 1);
		}
		writer.sectionEnd().close();
	}

	/**
	 * Check if an array of tags includes an {@code @after} tag.
	 *
	 * @param inlineTags
	 *                   array of tags
	 * @return {@code true} if and only if the tags include an {@code @after}
	 */
	private boolean hasAfterTag(Tag[] inlineTags) {
		for (Tag tag : inlineTags) {
			if (tag.name().equals("@after")) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Generate documentation for the given class.
	 *
	 * @param classDoc
	 *                 class to document
	 * @throws IOException
	 *                     if some I/O error occurred
	 */
	private void generateClass(ClassDoc classDoc) throws IOException {
		MdWriter writer = new MdWriter(destination, classDoc.name(), classDoc.name(), true);
		generatePackageSidebar(writer);
		writer.section("main class").h1("{{ page.title | escape }}");
		writer.tags(classDoc.inlineTags());
		// FIELDS
		FieldDoc[] fields = classDoc.fields();
		if (fields.length > 0) {
			int numberOfConstants = 0;
			for (FieldDoc field : fields) {
				if (field.isStatic() && field.isFinal()) {
					numberOfConstants++;
				}
			}
			if (numberOfConstants > 0) {
				// writer.h2("Constants");
				for (FieldDoc field : fields) {
					if (field.isStatic() && field.isFinal()) {
						writer.h2(null, field.name(), field.name());
						writer.prejava();
						writer.cdata(field.modifiers() + " ");
						writer.cdata(excludeQualifier(field.type().qualifiedTypeName()) + " ");
						writer.cdata(field.name());
						String value = field.constantValueExpression();
						if (value != null) {
							writer.cdata(" = " + value);
						}
						writer.cdata("\n").prejavaEnd();
						writer.p().tags(field.inlineTags()).pEnd();
					}
				}
			}
			if (numberOfConstants < fields.length) {
				// writer.h2("Fields");
				for (FieldDoc field : fields) {
					if (!field.isStatic() || !field.isFinal()) {
						writer.h2(null, field.name(), field.name());
						writer.prejava();
						writer.cdata(field.modifiers() + " ");
						writer.cdata(excludeQualifier(field.type().qualifiedTypeName()) + " ");
						writer.cdata(field.name());
						writer.cdata("\n").prejavaEnd();
						writer.p().tags(field.inlineTags()).pEnd();
					}
				}
			}
		}
		// CONSTRUCTORS
		ConstructorDoc[] constructors = classDoc.constructors();
		if (constructors.length > 0) {
			// writer.h2("Constructors");
			for (ConstructorDoc constructor : constructors) {
				writer.h2(null, constructor.name(), constructor.name() + constructor.flatSignature());
				writer.prejava();
				writer.cdata(constructor.modifiers() + " ");
				generateMethodHead(writer, constructor);
				writer.prejavaEnd();
				generateMethod(writer, constructor);
			}
		}
		// METHODS
		MethodDoc[] methods = classDoc.methods();
		if (methods.length > 0) {
			// writer.h2("Methods");
			for (MethodDoc method : methods) {
				writer.h2(null, method.name(), method.name() + method.flatSignature());
				writer.prejava();
				writer.cdata(method.modifiers() + " ");
				writer.cdata(excludeQualifier(method.returnType().qualifiedTypeName()) + " ");
				generateMethodHead(writer, method);
				writer.prejavaEnd();
				generateMethod(writer, method);
			}
		}
		writer.sectionEnd();
		generateClassSidebar(writer, classDoc);
		writer.close();
	}

	/**
	 * Generate a short summary for the given method.
	 *
	 * @param writer
	 *                   markdown writer to generate document with
	 * @param executable
	 *                   method information
	 */
	private void generateMethodHead(MdWriter writer, ExecutableMemberDoc executable) {
		writer.cdata(executable.name() + "(");
		Parameter[] params = executable.parameters();
		if (params.length > 0) {
			boolean isFirst = true;
			for (Parameter param : params) {
				if (isFirst) {
					isFirst = false;
				} else {
					writer.cdata(", ");
				}
				writer.cdata(excludeQualifier(param.type().qualifiedTypeName()) + " ");
				writer.cdata(param.name());
			}
		}
		writer.cdata(")\n");
	}

	/**
	 * Generate detailed documentation for the given method.
	 *
	 * @param writer
	 *                   markdown writer to generate document with
	 * @param executable
	 *                   method information
	 */
	private void generateMethod(MdWriter writer, ExecutableMemberDoc executable) {
		writer.tags(executable.inlineTags());
		Parameter[] params = executable.parameters();
		ParamTag[] paramTags = executable.paramTags();
		if (params.length > 0) {
			writer.h4("Parameters").table("parameters").tbody();
			for (int i = 0, n = params.length; i < n; i++) {
				writer.tr();
				writer.td().cdata(params[i].name()).cdata("<br/>");
				writer.span("paramtype").cdata(excludeQualifier(params[i].type().qualifiedTypeName())).spanEnd();
				writer.tdEnd();
				if (i < paramTags.length) {
					writer.td().tags(paramTags[i].inlineTags()).tdEnd();
				} else {
					writer.td().tdEnd();
				}
				writer.trEnd();
			}
			writer.tbodyEnd().tableEnd();
		}
		Tag[] returnTags = executable.tags("@return");
		if (returnTags.length > 0) {
			writer.h4("Returns");
			writer.p().tags(returnTags[0].inlineTags()).pEnd();
		}
		// writer.h4("Throws");
	}

	/**
	 * Output a sidebar for a class page.
	 *
	 * @param writer
	 *                 markdown writer to write to
	 * @param classDoc
	 *                 class documentation root
	 * @throws IOException
	 *                     if some I/O error occurred
	 */
	private void generateClassSidebar(MdWriter writer, ClassDoc classDoc) throws IOException {
		writer.section("apitoc").ul("section-nav");
		FieldDoc[] fields = classDoc.fields();
		if (fields.length > 0) {
			Arrays.sort(fields);
			int numberOfConstants = 0;
			for (FieldDoc field : fields) {
				if (field.isStatic() && field.isFinal()) {
					numberOfConstants++;
				}
			}
			if (numberOfConstants > 0) {
				writer.li("toc-entry toc-h2").cdata("Constants").ul();
				for (FieldDoc field : fields) {
					if (field.isStatic() && field.isFinal()) {
						writer.li("toc-entry toc-h3").a(classDoc.name() + "#" + field.name(), field.name()).liEnd();
					}
				}
				writer.ulEnd().liEnd();
			}
			if (numberOfConstants < fields.length) {
				writer.li("toc-entry toc-h2").cdata("Fields").ul();
				for (FieldDoc field : fields) {
					if (!field.isStatic() || !field.isFinal()) {
						writer.li("toc-entry toc-h3").a(classDoc.name() + "#" + field.name(), field.name()).liEnd();
					}
				}
				writer.ulEnd().liEnd();
			}
		}
		ConstructorDoc[] constructors = classDoc.constructors();
		if (constructors.length > 0) {
			Arrays.sort(constructors);
			writer.li("toc-entry toc-h2").cdata("Constructors").ul();
			for (ConstructorDoc constructor : constructors) {
				String text = constructor.name() + constructor.flatSignature();
				String anchor = classDoc.name() + "#" + text;
				writer.li("toc-entry toc-h3");
				writer.a(anchor, text);
				writer.liEnd();
			}
			writer.ulEnd().liEnd();
		}
		MethodDoc[] methods = classDoc.methods();
		if (methods.length > 0) {
			Arrays.sort(methods);
			writer.li("toc-entry toc-h2").cdata("Methods").ul();
			for (MethodDoc method : methods) {
				String text = method.name() + method.flatSignature();
				String anchor = classDoc.name() + "#" + text;
				writer.li("toc-entry toc-h3");
				writer.a(anchor, text);
				writer.liEnd();
			}
			writer.ulEnd().liEnd();
		}
		writer.cdata("\n").ulEnd().sectionEnd();
	}

	/**
	 * Output a sidebar for a package page.
	 *
	 * @param writer
	 *               markdown writer to write to
	 * @throws IOException
	 *                     if some I/O error occurred
	 */
	private void generatePackageSidebar(MdWriter writer) throws IOException {
		writer.section("sidetoc").ul("section-nav");
		writer.li("toc-entry toc-h2").ax("top", "/api/", "API home").liEnd();
		writer.li("toc-entry toc-h2").cdata("GREEN").ul();
		for (PackageDoc packageDoc : greenPackages) {
			writer.li("toc-entry toc-h3").a(packageDoc.name(), packageDoc.name()).liEnd();
		}
		writer.ulEnd().liEnd().ulEnd().sectionEnd();
	}

	/**
	 * Return the collection as a sorted array.
	 *
	 * @param <T>
	 *                   runtime type of the collection
	 * @param collection
	 *                   collection to sort
	 * @return sorted version of the collection
	 */
	@SuppressWarnings("unchecked")
	private <T> T[] sortList(Collection<T> collection) {
		SortedSet<T> sortedSet = new TreeSet<>(collection);
		return (T[]) sortedSet.toArray();
	}

	/**
	 * Sort and return, but do not modify, an array.
	 *
	 * @param <T>
	 *                   runtime type of the array
	 * @param collection
	 *                   array to sort
	 * @return sorted version of the array
	 */
	@SuppressWarnings("unchecked")
	private <T> T[] sortList(T[] collection) {
		SortedSet<T> sortedSet = new TreeSet<>();
		for (T t : collection) {
			sortedSet.add(t);
		}
		return (T[]) sortedSet.toArray();
	}

	// ======================================================================
	//
	// MDWRITER CLASS
	//
	// ======================================================================

	/**
	 * File separator for this operating system.
	 */
	private static final String FILE_SEPARATOR = System.getProperty("file.separator");

	/**
	 * Create an output writer to support a markdown writer ({@link MdWriter}) with
	 * a given filename.
	 *
	 * @param fullFilename
	 *                     name of file to write to
	 * @return writer that will output to file
	 * @throws IOException
	 *                     if some I/O error occurred
	 */
	private static Writer generateWriter(String fullFilename) throws IOException {
		FileOutputStream fos = new FileOutputStream(fullFilename);
		return new OutputStreamWriter(fos, "UTF-8");
	}

	/**
	 * Markdown writer for documentation.
	 */
	public class MdWriter extends PrintWriter {

		/**
		 * Create a markdown writer for a given path and document title.
		 * 
		 * @param path
		 *              path for the markdown writer
		 * @param title
		 *              title of the document
		 * @throws IOException
		 *                     if some I/O error occurred
		 */
		public MdWriter(String path, String title) throws IOException {
			super(generateWriter(path + FILE_SEPARATOR + "index.md"));
			writeFrontMatter(title, "/api/");
		}

		/**
		 * Create a markdown writer for a given path and document title with a flag to
		 * indicate of the table of content should be generated. If the {@code toc}
		 * parameter is {@code true}, this property is added to the frontmatter of the
		 * generated page.
		 * 
		 * @param path
		 *              path for the markdown writer
		 * @param title
		 *              title of the document
		 * @param toc
		 *              whether or not the "toc" property is set in the frontmatter
		 * @throws IOException
		 *                     if some I/O error occurred
		 */
		public MdWriter(String path, String title, boolean toc) throws IOException {
			super(generateWriter(path + FILE_SEPARATOR + "index.md"));
			writeFrontMatter(title, "/api/", new Object[][] { { "toc", toc } });
		}

		/**
		 * Create a markdown writer for a given path and filename, and document title.
		 * 
		 * @param path
		 *                 path for the markdown writer
		 * @param filename
		 *                 filename for the markdown writer
		 * @param title
		 *                 title of the document
		 * @throws IOException
		 *                     if some I/O error occurred
		 */
		public MdWriter(String path, String filename, String title) throws IOException {
			super(generateWriter(path + FILE_SEPARATOR + filename + ".md"));
			writeFrontMatter(title, String.format("/api/%s/", filename));
		}

		/**
		 * Create a markdown writer for a given path and filename, and document title
		 * with a flag to indicate of the table of content should be generated. If the
		 * {@code toc} parameter is {@code true}, this property is added to the
		 * frontmatter of the generated page.
		 * 
		 * @param path
		 *                 path for the markdown writer
		 * @param filename
		 *                 filename for the markdown writer
		 * @param title
		 *                 title of the document
		 * @param toc
		 *                 whether or not the "toc" property is set in the frontmatter
		 * @throws IOException
		 *                     if some I/O error occurred
		 */
		public MdWriter(String path, String filename, String title, boolean toc) throws IOException {
			super(generateWriter(path + FILE_SEPARATOR + filename + ".md"));
			writeFrontMatter(title, String.format("/api/%s/", filename), new Object[][] { { "toc", toc } });
		}

		/**
		 * Output the markdown frontmatter given the page title, permalink, and optional
		 * additional markdown frontmatter tags. The tags are expected to be arranged in
		 * pairs: tag1, value1, tag2, value2, tag3, value3, ...
		 *
		 * @param title
		 *                  title of the page
		 * @param permalink
		 *                  permalink for the page
		 * @param extras
		 *                  array of additional tags
		 */
		private void writeFrontMatter(String title, String permalink, Object[]... extras) {
			println("---");
			printf("title: %s\n", title);
			printf("permalink: %s\n", permalink);
			for (Object[] extra : extras) {
				printf("%s: %s\n", extra[0].toString(), extra[1].toString());
			}
			println("---\n");
		}

		/**
		 * Output an array of Javadoc tags as markdown. The {@code before} parameter
		 * controls how {@code @after} tags are handled. If it is negative, output
		 * generation terminates as soon as the first {@code @after} tag is encountered.
		 * If it is positive, output generation starts at the first {@code @after} tag.
		 *
		 * @param tags
		 *               array of tags to output
		 * @param before
		 *               {@code @after} control flag
		 * @return reference to this markdown writer
		 */
		private MdWriter tags(Tag[] tags, int before) {
			int i = 0;
			if (before > 0) {
				while ((i < tags.length) && !tags[i].name().equals("@after")) {
					i++;
				}
			}
			while (i < tags.length) {
				switch (tags[i].name()) {
				case "@after":
					if (before < 0) {
						return this;
					}
					break;
				case "Text":
					cdata(tags[i].text());
					break;
				case "@prejava":
					prejava().cdata(tags[i].text()).prejavaEnd();
					break;
				case "@link":
					code().az(tags[i].holder(), null, tags[i].text(), tags[i].text()).codeEnd();
					break;
				case "@code":
					code().cdata(tags[i].text()).codeEnd();
					break;
				default:
					cdata("TAG(" + tags[i].name() + ", " + tags[i].text() + ")");
					break;
				}
				i++;
			}
			return this;
		}

		/**
		 * Output an array of Javadoc tags as markdown. If the tags contains an
		 * {@code @after} tag, only tags *after* the tag is generated.
		 *
		 * @param tags
		 *             array of tags to output
		 * @return reference to this markdown writer
		 */
		private MdWriter tags(Tag[] tags) {
			return tags(tags, 0);
		}

		/**
		 * Output an HTML A element for a given URL and text.
		 *
		 * @param href
		 *             original URL for link
		 * @param text
		 *             text for link
		 * @return reference to this markdown writer
		 */
		public MdWriter a(String href, String text) {
			printf("<a href=\"%s\">%s</a>", href(href), text);
			return this;
		}

		/**
		 * Output an HMTL A element for a given URL, text, and class.
		 *
		 * @param clas
		 *             class for the element
		 * @param href
		 *             original URL for link
		 * @param text
		 *             text for link
		 * @return reference to this markdown writer
		 */
		public MdWriter a(String clas, String href, String text) {
			printf("<a class=\"%s\" href=\"%s\">%s</a>\n", clas, href(href), text);
			return this;
		}

		/**
		 * Output an HMTL A element for a given URL, text, and class for internal links.
		 * The URL is generated as a markdown link.
		 *
		 * @param clas
		 *             class for the element
		 * @param href
		 *             original URL for link
		 * @param text
		 *             text for link
		 * @return reference to this markdown writer
		 */
		public MdWriter ax(String clas, String href, String text) {
			printf("<a class=\"%s\" href=\"{{ '%s' | relative_url }}\">%s</a>\n", clas, href, text);
			return this;
		}

		/**
		 * Output an HMTL A element for a given URL, text, and class for internal links
		 * in a given document. The URL is generated as a markdown link.
		 *
		 * @param doc
		 *             documentation root
		 * @param clas
		 *             class for the element
		 * @param href
		 *             original URL for link
		 * @param text
		 *             text for link
		 * @return reference to this markdown writer
		 */
		public MdWriter az(Doc doc, String clas, String href, String text) {
			String classSpec = "";
			if (clas != null) {
				classSpec = String.format(" class=\"%s\"", clas);
			}
			if (href.startsWith("#")) {
				printf("<a%s href=\"%s\">%s</a>\n", classSpec, href(doc.name() + href), text.substring(1));
				return this;
			} else {
				printf("<a%s href=\"%s\">%s</a>\n", classSpec, href(href), text);
				return this;
			}
		}

		/**
		 * Return a markdown-style version of a URL that takes anchors into account.
		 *
		 * @param href
		 *             original URL
		 * @return markdown URL
		 */
		private String href(String href) {
			int index = href.indexOf('#');
			if (index == -1) {
				return String.format("{{ '/api/%s/' | relative_url }}", href);
			} else {
				String anchor = href.substring(index);
				String base = href.substring(0, index);
				return String.format("{{ '/api/%s/' | relative_url }}%s", base, anchor);
			}
		}

		/**
		 * Write raw data.
		 *
		 * @param data
		 *             data to write
		 * @return reference to this markdown writer
		 */
		public MdWriter cdata(String data) {
			print(data);
			return this;
		}

		/**
		 * Generate start of preformatted Java code.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter prejava() {
			println("<div markdown=\"1\">");
			println("~~~java");
			return this;
		}

		/**
		 * Generate end of preformatted Java code.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter prejavaEnd() {
			println("~~~");
			println("</div>");
			return this;
		}

		/**
		 * Generate start of an HTML paragraph.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter p() {
			return generic("p");
		}

		/**
		 * Generate start of an HTML paragraph with a given class.
		 *
		 * @param clas
		 *             class for the heading
		 * @return reference to this markdown writer
		 */
		public MdWriter p(String clas) {
			return generic(clas, "p");
		}

		/**
		 * Generate end of an HTML paragraph.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter pEnd() {
			return genericEnd("p");
		}

		/**
		 * Generate start of an HTML span.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter span() {
			return generic("span", false);
		}

		/**
		 * Generate start of an HTML span with a given class.
		 *
		 * @param clas
		 *             class for the heading
		 * @return reference to this markdown writer
		 */
		public MdWriter span(String clas) {
			return generic(clas, "span", false);
		}

		/**
		 * Generate end of an HTML span.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter spanEnd() {
			return genericEnd("span", false);
		}

		/**
		 * Generate start of an HTML code element.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter code() {
			return generic("code", false);
		}

		/**
		 * Generate start of an HTML code element with a given class.
		 *
		 * @param clas
		 *             class for the heading
		 * @return reference to this markdown writer
		 */
		public MdWriter code(String clas) {
			return generic(clas, "code", false);
		}

		/**
		 * Generate end of an HTML code element.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter codeEnd() {
			return genericEnd("code", false);
		}

		/**
		 * Generate start of an HTML element.
		 *
		 * @param element
		 *                name of the element
		 * @return reference to this markdown writer
		 */
		private MdWriter generic(String element) {
			return generic(element, true);
		}

		/**
		 * Generate start of an HTML element with a given class.
		 *
		 * @param clas
		 *                class for the heading
		 * @param element
		 *                name of the element
		 * @return reference to this markdown writer
		 */
		private MdWriter generic(String clas, String element) {
			return generic(clas, element, true);
		}

		/**
		 * Generate end of an HTML element.
		 *
		 * @param element
		 *                name of the element
		 * @return reference to this markdown writer
		 */
		private MdWriter genericEnd(String element) {
			return genericEnd(element, true);
		}

		/**
		 * Generate start of an HTML element with optional new line.
		 *
		 * @param element
		 *                name of the element
		 * @param newline
		 *                flag to indicate if new line is needed
		 * @return reference to this markdown writer
		 */
		private MdWriter generic(String element, boolean newline) {
			printf("<%s>", element);
			if (newline) {
				printf("\n");
			}
			return this;
		}

		/**
		 * Generate start of an HTML element with given class and optional new line.
		 *
		 * @param clas
		 *                class for the heading
		 * @param element
		 *                name of the element
		 * @param newline
		 *                flag to indicate if new line is needed
		 * @return reference to this markdown writer
		 */
		private MdWriter generic(String clas, String element, boolean newline) {
			if (clas == null) {
				printf("<%s>", element);
			} else {
				printf("<%s class=\"%s\">", element, clas);
			}
			if (newline) {
				printf("\n");
			}
			return this;
		}

		/**
		 * Generate end of an HTML element with optional new line.
		 *
		 * @param element
		 *                name of the element
		 * @param newline
		 *                flag to indicate if new line is needed
		 * @return reference to this markdown writer
		 */
		private MdWriter genericEnd(String element, boolean newline) {
			printf("</%s>", element);
			if (newline) {
				printf("\n");
			}
			return this;
		}

		// ======================================================================
		//
		// HEADINGS
		//
		// ======================================================================

		/**
		 * Generate an HTML H1 heading.
		 *
		 * @param heading
		 *                heading text
		 * @return reference to this markdown writer
		 */
		public MdWriter h1(String heading) {
			return hn("h1", heading);
		}

		/**
		 * Generate an HTML H1 heading with a given class.
		 *
		 * @param clas
		 *                class for the heading
		 * @param heading
		 *                heading text
		 * @return reference to this markdown writer
		 */
		public MdWriter h1(String clas, String heading) {
			return hn("h1", clas, heading);
		}

		/**
		 * Generate an HTML H1 heading with a given class.
		 *
		 * @param clas
		 *                class for the heading
		 * @param heading
		 *                heading text
		 * @param name
		 *                anchor name for the heading
		 * @return reference to this markdown writer
		 */
		public MdWriter h1(String clas, String heading, String name) {
			return hn("h1", clas, heading, name);
		}

		/**
		 * Generate an HTML H2 heading.
		 *
		 * @param heading
		 *                heading text
		 * @return reference to this markdown writer
		 */
		public MdWriter h2(String heading) {
			return hn("h2", heading);
		}

		/**
		 * Generate an HTML H2 heading with a given class.
		 *
		 * @param clas
		 *                class for the heading
		 * @param heading
		 *                heading text
		 * @return reference to this markdown writer
		 */
		public MdWriter h2(String clas, String heading) {
			return hn("h2", clas, heading);
		}

		/**
		 * Generate an HTML H2 heading with a given class and anchor.
		 *
		 * @param clas
		 *                class for the heading
		 * @param heading
		 *                heading text
		 * @param name
		 *                anchor name for the heading
		 * @return reference to this markdown writer
		 */
		public MdWriter h2(String clas, String heading, String name) {
			return hn("h2", clas, heading, name);
		}

		/**
		 * Generate an HTML H3 heading.
		 *
		 * @param heading
		 *                heading text
		 * @return reference to this markdown writer
		 */
		public MdWriter h3(String heading) {
			return hn("h3", heading);
		}

		/**
		 * Generate an HTML H3 heading with a given class.
		 *
		 * @param clas
		 *                class for the heading
		 * @param heading
		 *                heading text
		 * @return reference to this markdown writer
		 */
		public MdWriter h3(String clas, String heading) {
			return hn("h3", clas, heading);
		}

		/**
		 * Generate an HTML H3 heading with a given class and anchor.
		 *
		 * @param clas
		 *                class for the heading
		 * @param heading
		 *                heading text
		 * @param name
		 *                anchor name for the heading
		 * @return reference to this markdown writer
		 */
		public MdWriter h3(String clas, String heading, String name) {
			return hn("h3", clas, heading, name);
		}

		/**
		 * Generate an HTML H4 heading.
		 *
		 * @param heading
		 *                heading text
		 * @return reference to this markdown writer
		 */
		public MdWriter h4(String heading) {
			return hn("h4", heading);
		}

		/**
		 * Generate an HTML H4 heading with a given class.
		 *
		 * @param clas
		 *                class for the heading
		 * @param heading
		 *                heading text
		 * @return reference to this markdown writer
		 */
		public MdWriter h4(String clas, String heading) {
			return hn("h4", clas, heading);
		}

		/**
		 * Generate an HTML H4 heading with a given class and anchor.
		 *
		 * @param clas
		 *                class for the heading
		 * @param heading
		 *                heading text
		 * @param name
		 *                anchor name for the heading
		 * @return reference to this markdown writer
		 */
		public MdWriter h4(String clas, String heading, String name) {
			return hn("h4", clas, heading, name);
		}

		/**
		 * Generate an HTML HN heading.
		 *
		 * @param hn
		 *                name of the heading element
		 * @param heading
		 *                heading text
		 * @return reference to this markdown writer
		 */
		private MdWriter hn(String hn, String heading) {
			printf("<%s>%s</%s>\n", hn, heading, hn);
			return this;
		}

		/**
		 * Generate an HTML HN heading with a given class.
		 *
		 * @param hn
		 *                name of the heading element
		 * @param clas
		 *                class for the heading
		 * @param heading
		 *                heading text
		 * @return reference to this markdown writer
		 */
		private MdWriter hn(String hn, String clas, String heading) {
			if (clas == null) {
				printf("<%s>%s</%s>\n", hn, heading, hn);
			} else {
				printf("<%s class=\"%s\">%s</%s>\n", hn, clas, heading, hn);
			}
			return this;
		}

		/**
		 * Generate an HTML HN heading with a given class and anchor.
		 *
		 * @param hn
		 *                name of the heading element
		 * @param clas
		 *                class for the heading
		 * @param heading
		 *                heading text
		 * @param name
		 *                anchor name for the heading
		 * @return reference to this markdown writer
		 */
		private MdWriter hn(String hn, String clas, String heading, String name) {
			if (clas == null) {
				printf("<%s><a class=\"anchor\" name=\"%s\"></a>%s</%s>\n", hn, name, heading, hn);
			} else {
				printf("<%s class=\"%s\"><a class=\"anchor\" name=\"%s\"></a>%s</%s>\n", hn, clas, name, heading, hn);
			}
			return this;
		}

		// ======================================================================
		//
		// LISTS
		//
		// ======================================================================

		/**
		 * Generate start of HTML bulleted list.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter ul() {
			return generic("ul");
		}

		/**
		 * Generate start of HTML bulleted list.
		 *
		 * @param clas
		 *             class for the list
		 * @return reference to this markdown writer
		 */
		public MdWriter ul(String clas) {
			return generic(clas, "ul");
		}

		/**
		 * Generate end of HTML bulleted list.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter ulEnd() {
			return genericEnd("ul");
		}

		/**
		 * Generate start of HTML list item.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter li() {
			return generic("li");
		}

		/**
		 * Generate start of HTML list item.
		 *
		 * @param clas
		 *             class for the list item
		 * @return reference to this markdown writer
		 */
		public MdWriter li(String clas) {
			return generic(clas, "li");
		}

		/**
		 * Generate end of HTML list item.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter liEnd() {
			return genericEnd("li");
		}

		// ======================================================================
		//
		// SECTIONS
		//
		// ======================================================================

		/**
		 * Generate start of HTML section.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter section() {
			return generic("section");
		}

		/**
		 * Generate start of HTML section with a given class.
		 *
		 * @param clas
		 *             class for the section
		 * @return reference to this markdown writer
		 */
		public MdWriter section(String clas) {
			return generic(clas, "section");
		}

		/**
		 * Generate end of HTML section.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter sectionEnd() {
			return genericEnd("section");
		}

		// ======================================================================
		//
		// TABLES
		//
		// ======================================================================

		/**
		 * Generate start of HTML table.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter table() {
			return generic("table");
		}

		/**
		 * Generate start of HTML table with a given class.
		 *
		 * @param clas
		 *             class for the table
		 * @return reference to this markdown writer
		 */
		public MdWriter table(String clas) {
			return generic(clas, "table");
		}

		/**
		 * Generate end of HTML table.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter tableEnd() {
			return genericEnd("table");
		}

		/**
		 * Generate start of HTML table head.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter thead() {
			return generic("thead");
		}

		/**
		 * Generate start of HTML table head with a given class.
		 *
		 * @param clas
		 *             class for the table head
		 * @return reference to this markdown writer
		 */
		public MdWriter thead(String clas) {
			return generic(clas, "thead");
		}

		/**
		 * Generate end of HTML table head.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter theadEnd() {
			return genericEnd("thead");
		}

		/**
		 * Generate start of HTML table body.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter tbody() {
			return generic("tbody");
		}

		/**
		 * Generate start of HTML table body with a given class.
		 *
		 * @param clas
		 *             class for the table body
		 * @return reference to this markdown writer
		 */
		public MdWriter tbody(String clas) {
			return generic(clas, "tbody");
		}

		/**
		 * Generate end of HTML table body.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter tbodyEnd() {
			return genericEnd("tbody");
		}

		/**
		 * Generate start of HTML table row.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter tr() {
			return generic("tr");
		}

		/**
		 * Generate start of HTML table row with a given class.
		 *
		 * @param clas
		 *             class for the table row
		 * @return reference to this markdown writer
		 */
		public MdWriter tr(String clas) {
			return generic(clas, "tr");
		}

		/**
		 * Generate end of HTML table row.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter trEnd() {
			return genericEnd("tr");
		}

		/**
		 * Generate start of HTML table header cell.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter th() {
			return generic("th");
		}

		/**
		 * Generate start of HTML table header cell with a given class.
		 *
		 * @param clas
		 *             class for the table header cell
		 * @return reference to this markdown writer
		 */
		public MdWriter th(String clas) {
			return generic(clas, "th");
		}

		/**
		 * Generate end of HTML table header cell.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter thEnd() {
			return genericEnd("th");
		}

		/**
		 * Generate start of HTML table data cell.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter td() {
			return generic("td");
		}

		/**
		 * Generate start of HTML table data cell with a given class.
		 *
		 * @param clas
		 *             class for the data cell
		 * @return reference to this markdown writer
		 */
		public MdWriter td(String clas) {
			return generic(clas, "td");
		}

		/**
		 * Generate end of HTML table data cell.
		 *
		 * @return reference to this markdown writer
		 */
		public MdWriter tdEnd() {
			return genericEnd("td");
		}

	}

}
