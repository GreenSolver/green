package za.ac.sun.cs.green.service;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.util.Reporter;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public abstract class ModelCoreService extends BasicService {

	private static final String SERVICE_KEY = "MODELCORE:";

	public static final String SAT_KEY = SERVICE_KEY + "SAT";

	public static final String MODEL_KEY = SERVICE_KEY + "MODEL";

	public static final String CORE_KEY = SERVICE_KEY + "CORE";

	private int invocationCount = 0;

	private int cacheHitCount = 0;

	private int cacheMissCount = 0;

	private long timeConsumption = 0;

	public ModelCoreService(Green solver) {
		super(solver);
	}

	@Override
	public void report(Reporter reporter) {
		reporter.report(getClass().getSimpleName(), "invocationCount = " + invocationCount);
		reporter.report(getClass().getSimpleName(), "cacheHitCount = " + cacheHitCount);
		reporter.report(getClass().getSimpleName(), "cacheMissCount = " + cacheMissCount);
		reporter.report(getClass().getSimpleName(), "timeConsumption = " + timeConsumption);
	}

	@Override
	public Object allChildrenDone(Instance instance, Object result) {
		return instance;
	}
	
	@Override
	public Set<Instance> processRequest(Instance instance) {
		if (instance.getData(SAT_KEY) == null) {
			solve0(instance);
		}
		return null;
	}

	@SuppressWarnings("unchecked")
	private void solve0(Instance instance) {
		invocationCount++;
		/*--- NO CACHING: ---*
		cacheMissCount++;
		ModelCore modelCore = solve1(instance);
		Boolean isSat = modelCore.getIsSat();
		instance.setData(SAT_KEY, isSat);
		if (isSat) {
			instance.setData(MODEL_KEY, modelCore.getModel());
		} else {
			instance.setData(CORE_KEY, modelCore.getCore());
		}
		/*------*/
		
		/*--- EXPERIMENTAL CACHING: ---*/
		Map<Variable, Constant> model = null;
		Set<Expression> core = null;
		String key = SERVICE_KEY + instance.getFullExpression().toString();
		Boolean isSat = (Boolean) store.get(key + "-SAT");
		if (isSat == null) {
			cacheMissCount++;
			ModelCore modelCore = solve1(instance);
			isSat = modelCore.getIsSat();
			store.put(key + "-SAT", isSat);
			if (isSat) {
				model = modelCore.getModel();
				store.put(key + "-MODEL", (HashMap<Variable, Constant>) model);
			} else {
				core = modelCore.getCore();
				store.put(key + "-CORE", (HashSet<Expression>) core);
			}
		} else {
			if (isSat) {
				model = (HashMap<Variable, Constant>) store.get(key + "-MODEL");
			} else {
				core = (HashSet<Expression>) store.get(key + "-CORE");
			}
			cacheHitCount++;
		}
		instance.setData(SAT_KEY, isSat);
		if (isSat) {
			instance.setData(MODEL_KEY, model);
		} else {
			instance.setData(CORE_KEY, core);
		}
		/*------*/
	}

	private ModelCore solve1(Instance instance) {
		long startTime = System.currentTimeMillis();
		ModelCore modelCore = modelCore(instance);
		timeConsumption += System.currentTimeMillis() - startTime;
		return modelCore;
	}

	protected abstract ModelCore modelCore(Instance instance);

	public static final Boolean isSat(Instance instance) {
		return (Boolean) instance.getData(SAT_KEY);
	}

	@SuppressWarnings("unchecked")
	public static final Map<Variable, Constant> getModel(Instance instance) {
		return (Map<Variable, Constant>) instance.getData(MODEL_KEY);
	}

	@SuppressWarnings("unchecked")
	public static final Set<Expression> getCore(Instance instance) {
		return (Set<Expression>) instance.getData(CORE_KEY);
	}

	public static class ModelCore {
		private final Boolean isSat;
		private final Map<Variable, Constant> model;
		private final Set<Expression> core;
		public ModelCore(final Boolean isSat, final Map<Variable, Constant> model, final Set<Expression> core) {
			this.isSat = isSat;
			this.model = model;
			this.core = core;
		}
		public Boolean getIsSat() { return isSat; }
		public Map<Variable, Constant> getModel() { return model; }
		public Set<Expression> getCore() { return core; }
	}
}
