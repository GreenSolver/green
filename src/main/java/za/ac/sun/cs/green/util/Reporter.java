package za.ac.sun.cs.green.util;

public abstract class Reporter {

	protected String context = "???";

	public final void setContext(String context) {
		this.context = context;
	}

	public final void report(String context, String key, int value) {
		report(context, key, Integer.toString(value));
	}

	public final void report(String context, String key, long value) {
		report(context, key, Long.toString(value));
	}
	
	public final void report(String context, String key, double value) {
		report(context, key, Double.toString(value));
	}
	
	public final void report(String key, String value) {
		report(context, key, value);
	}
	
	public final void report(String key, int value) {
		report(context, key, Integer.toString(value));
	}
	
	public final void report(String key, long value) {
		report(context, key, Long.toString(value));
	}
	
	public final void report(String key, double value) {
		report(context, key, Double.toString(value));
	}
	
	public void reportMessage(String message) {
		reportMessage(context, message);
	}
	
	public abstract void reportMessage(String context, String message);
	
	public abstract void report(String context, String key, String value);

}
