package za.ac.sun.cs.green.service;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.service.grulia.SatEntry;
import za.ac.sun.cs.green.service.grulia.UnsatEntry;
import za.ac.sun.cs.green.util.Reporter;

import java.util.Map;
import java.util.Set;

public abstract class ModelCoreService extends BasicService {

	public static final String SERVICE_KEY = "MODELCORE:";

	public static final String SAT_KEY = SERVICE_KEY + "SAT";

	public static final String MODEL_KEY = SERVICE_KEY + "MODEL";

	public static final String CORE_KEY = SERVICE_KEY + "CORE";

	private int invocationCount = 0;

	protected int cacheHitCount = 0;
	protected int satHitCount = 0;
	protected int unsatHitCount = 0;

	protected int cacheMissCount = 0;
	protected int satMissCount = 0;
	protected int unsatMissCount = 0;

	private long timeConsumption = 0;
	protected long storageTimeConsumption = 0;

	protected int satCount = 0;
	protected int unsatCount = 0;

	public ModelCoreService(Green solver) {
		super(solver);
	}

	@Override
	public void report(Reporter reporter) {
		reporter.setContext(getClass().getSimpleName());
		reporter.report("invocationCount", invocationCount);
		reporter.report("cacheHitCount", cacheHitCount);
		reporter.report("satCacheHitCount", satHitCount);
		reporter.report("unsatCacheHitCount", unsatHitCount);
		reporter.report("cacheMissCount", cacheMissCount);
		reporter.report("satCacheMissCount", satMissCount);
		reporter.report("unsatCacheMissCount", unsatMissCount);
		reporter.report("timeConsumption", timeConsumption);
		reporter.report("storageTimeConsumption", storageTimeConsumption);
		reporter.report("satQueries", satCount);
		reporter.report("unssatQueries", unsatCount);
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
		SatEntry se = null;
		UnsatEntry ue = null;
//		String key = SERVICE_KEY + instance.getFullExpression().getString();
		String key = SERVICE_KEY + instance.getFullExpression().toString();
		long tmpConsumption = 0L;
		long start = System.currentTimeMillis();
		Boolean isSat = (Boolean) store.get(key + "-SAT");
		if (isSat == null) {
			cacheMissCount++;
			long startTime = System.currentTimeMillis();
			ModelCore modelCore = solve1(instance);
			timeConsumption += (System.currentTimeMillis() - startTime);
			tmpConsumption = System.currentTimeMillis() - startTime;
			isSat = modelCore.getIsSat();
			store.put(key + "-SAT", isSat);
			if (isSat) {
				satMissCount++;
				model = modelCore.getModel();
				se = new SatEntry(instance.getExpression().satDelta, model);
//				store.put(key + "-MODEL", (HashMap<Variable, Constant>) model);
				store.put(key + "-MODEL", se);
			} else {
				unsatMissCount++;
				core = modelCore.getCore();
				ue = new UnsatEntry(instance.getExpression().satDelta, core);
//                store.put(key + "-CORE", (HashSet<Expression>) core);
				store.put(key + "-CORE", ue);
			}
		} else {
			if (isSat) {
				satHitCount++;
//				model = (HashMap<Variable, Constant>) store.get(key + "-MODEL");
				se = (SatEntry) store.get(key + "-MODEL");
			} else {
				unsatHitCount++;
//				core = (HashSet<Expression>) store.get(key + "-CORE");
				ue = (UnsatEntry) store.get(key + "-CORE");
			}
			cacheHitCount++;
		}
		instance.setData(SAT_KEY, isSat);
		if (isSat) {
//			instance.setData(MODEL_KEY, model);
			instance.setData(MODEL_KEY, se);
		} else {
//			instance.setData(CORE_KEY, core);
			instance.setData(CORE_KEY, ue);
		}
		/*------*/
		storageTimeConsumption += ((System.currentTimeMillis() - start) - tmpConsumption);
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

	public static final Map<Variable, Constant> getModel(Instance instance) {
		return ((SatEntry) instance.getData(MODEL_KEY)).getSolution();
	}

	public static final Set<Expression> getCore(Instance instance) {
		return ((UnsatEntry) instance.getData(CORE_KEY)).getSolution();
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

		public Boolean getIsSat() {
			return isSat;
		}

		public Map<Variable, Constant> getModel() {
			return model;
		}

		public Set<Expression> getCore() {
			return core;
		}
	}
}
