import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map.Entry;
import gurobi.GRB;
import gurobi.GRBEnv;
import gurobi.GRBException;
import gurobi.GRBLinExpr;
import gurobi.GRBModel;
import gurobi.GRBVar;
import gurobi.GRB.DoubleAttr;
import gurobi.GRB.IntParam;

public class SubProblem {

	public GRBModel qModel;
	public static double precisionRC = 1e-7;

	public SubProblem() {
	}

	public SubProblem(GRBEnv env, String fileName, RMP rmp, int NoPb, boolean[][] adjacency, int[] clusters,
			double[] dualsCluster, int poolSize, int _n, int _k, int nrH) throws GRBException {
		GRBModel model = new GRBModel(env);
		model.set(GRB.IntParam.OutputFlag, 0);
		GRBVar[] chrsVars = new GRBVar[_n];
		GRBLinExpr expr, objFunction = new GRBLinExpr();

		for (int h = 0; h < _n; h++)
			chrsVars[h] = model.addVar(0, 1, 0, GRB.BINARY, "x" + h);
		model.update();

		for (int i = 0; i < _n; i++)
			for (int j = i + 1; j < _n; j++)
				if (adjacency[i][j]) {
					expr = new GRBLinExpr();
					expr.addTerm(1, chrsVars[i]);
					expr.addTerm(1, chrsVars[j]);
					model.addConstr(expr, GRB.LESS_EQUAL, 1.0, "Adjacent_" + i + "_" + j);
				}
		for (int h = 0; h < _k; h++) {
			expr = new GRBLinExpr();
			for (int i = 0; i < _n; i++)
				if (clusters[i] == h)
					expr.addTerm(1, chrsVars[i]);
			if (expr != null)
				model.addConstr(expr, GRB.LESS_EQUAL, 1.0, "ClusterIntrs_" + h);
		}

		expr = new GRBLinExpr();
		for (int i = 0; i < _n; i++)
			expr.addTerm(1, chrsVars[i]);
		model.addConstr(expr, GRB.GREATER_EQUAL, 2.0, "StableCardinality");

		objFunction = new GRBLinExpr();
		for (int i = 0; i < _n; i++)
			objFunction.addTerm(dualsCluster[clusters[i]] - 1, chrsVars[i]);
		model.setObjective(objFunction);
		model.set(GRB.IntAttr.ModelSense, GRB.MINIMIZE);
		model.set(GRB.IntParam.OutputFlag, 0);
		model.update();

		long st = System.nanoTime();
		this.qModel = model;
	}

	public SubProblem(GRBEnv env, String fileName, RMP rmp, int NoPb, boolean[][] adjacency, int[] clusters,
			double[] dualsCluster, int[] dualC_index, int poolSize, int _n, int _k, int nrH) throws GRBException {
		String path = "../data/PartitionCol/results/";
		GRBModel model = new GRBModel(env);
		model.set(GRB.IntParam.OutputFlag, 0);
		GRBVar[] chrsVars = new GRBVar[_n];
		GRBLinExpr expr, objFunction = new GRBLinExpr();

		for (int h = 0; h < _n; h++)
			chrsVars[h] = model.addVar(0, 1, 0, GRB.BINARY, "x" + h);
		model.update();

		for (int i = 0; i < _n; i++)
			for (int j = i + 1; j < _n; j++)
				if (adjacency[i][j]) {
					expr = new GRBLinExpr();
					expr.addTerm(1, chrsVars[i]);
					expr.addTerm(1, chrsVars[j]);
					model.addConstr(expr, GRB.LESS_EQUAL, 1.0, "Adjacent_" + i + "_" + j);
				}
		for (int h = 0; h < _k; h++) {
			expr = new GRBLinExpr();
			for (int i = 0; i < _n; i++)
				if (clusters[i] == h)
					expr.addTerm(1, chrsVars[i]);
			if (expr != null)
				model.addConstr(expr, GRB.LESS_EQUAL, 1.0, "ClusterIntrs_" + h);
		}

		expr = new GRBLinExpr();
		for (int i = 0; i < _n; i++)
			expr.addTerm(1, chrsVars[i]);
		model.addConstr(expr, GRB.GREATER_EQUAL, 2.0, "StableCardinality");

		objFunction = new GRBLinExpr();
		for (int i = 0; i < _n; i++)
			objFunction.addTerm(dualsCluster[clusters[i]] - 1, chrsVars[i]);
		model.setObjective(objFunction);
		model.set(GRB.IntAttr.ModelSense, GRB.MINIMIZE);
		model.set(GRB.IntParam.OutputFlag, 0);
		model.update();

		long st = System.nanoTime();
		System.out.println("h: " + nrH);
		this.qModel = model;
	}

	public ColorClass[] solvePool(String fileName, int _s, double precision, boolean[][] adjacency, int nrH,
			int poolSize) throws GRBException {
		int h, k;
		String varName;

		long st = System.nanoTime();
		this.qModel.set(IntParam.PoolSearchMode, 2);
		this.qModel.set(IntParam.PoolSolutions, poolSize);
		this.qModel.optimize();
		int sol_count = this.qModel.get(GRB.IntAttr.SolCount);
		this.qModel.update();
		ColorClass[] colorClasses = null;
		if (this.qModel.get(GRB.IntAttr.Status) != 2 || sol_count == 0)
			return null;
		if (this.qModel.get(DoubleAttr.ObjVal) < -1 - precision) {
			colorClasses = new ColorClass[sol_count];
			for (int l = 0; l < sol_count; l++) {
				this.qModel.set(IntParam.SolutionNumber, l);
				GRBVar[] vars = this.qModel.getVars();
				HashSet<Integer> nodes = new HashSet<Integer>();
				for (int p = 0; p < vars.length; p++) {
					varName = vars[p].get(GRB.StringAttr.VarName);
					h = varName.indexOf('x');
					if (h != -1) {
						k = Integer.valueOf(varName.substring(h + 1));
						if (vars[p].get(GRB.DoubleAttr.Xn) > 1.0 - 1e-7)
							nodes.add((Integer) k);
					}
				}
				colorClasses[l] = new ColorClass(nodes, adjacency);
			}
		}
		this.qModel.dispose();
		return colorClasses;
	}
}
