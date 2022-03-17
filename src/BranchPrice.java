import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Stack;
import java.util.Map.Entry;
import java.util.Random;
import java.util.Set;

import gurobi.GRB;
import gurobi.GRBConstr;
import gurobi.GRBEnv;
import gurobi.GRBException;
import gurobi.GRBLinExpr;
import gurobi.GRBModel;
import gurobi.GRBVar;
import gurobi.GRB.DoubleAttr;
import gurobi.GRB.IntParam;
import gurobi.GRB.StringAttr;

public class BranchPrice {
	// noOfClasses is the number of generated variables (-1);
	// n is the order of the graph;
	// m is the number of edges (the size);
	// k is the number of clusters;
	public static int n, m, k, noOfCreatedClasses = 0, noOfCreatedVertices = 0, noOfCreatedClusters = 0, Delta,
			noStages = 2, rootNoOfFacetsPerCluster, nodeNoOfFacetsPerCluster, nodeNoOfMajClqFacetsPerSize,
			rootNoOfMajClqFacetsPerSize;
	public static boolean deterministicInitialStage = true;
	public static boolean[][] adjacency;// adjacency matrix
	public static int[] clusters;// the clusters
	public static ColorClass[] clustersContent;
	public static Stack<RMP> stackRMPb = new Stack<RMP>();
	public static double precisionRC = 1e-6;// the reduced cost precision (if the reduced cost of a new variable is
											// greater than precisionRC, then that variable can be added to the model
	public static double precisionVar = 1e-9;
	public static double precisionOpt = 1e-8;
	public static double precisionBB = 1e-5;
	public static double precisionLB = 1e-5;
	public static double upperB = 1e20;
	public static double rootLowerB = -1e20;

	public static int[] readGraphSize(String dataFile) {
		int[] size = new int[2];
		String path = "../data/PartitionCol/", text = null;
		File file = new File(path + "instances/" + dataFile);
		BufferedReader reader = null;
		String[] nors = null;
		try {
			reader = new BufferedReader(new FileReader(file));
			text = reader.readLine();
			nors = text.split("\\s+", 0);
			size[0] = Integer.valueOf(nors[0]);
			size[1] = Integer.valueOf(nors[1]);
			size[2] = Integer.valueOf(nors[2]);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return size;
	}

	public static void readFile(String dataFile) {
		ReadGraphFromFile readGfF = new ReadGraphFromFile();
		int[] size = readGfF.readGraphSize(dataFile);
		n = size[0];
		noOfCreatedVertices = n;
		m = size[1];
		k = size[2];
		noOfCreatedClusters = k;
		System.out.println("File " + dataFile + " n = " + n + " m = " + m + " k = " + k);
		adjacency = new boolean[n][n];
		clusters = new int[n];
		clustersContent = new ColorClass[k];
		readGfF.readGraph(dataFile, adjacency, clusters, clustersContent);
		System.out.println("End reading from file");
	}

	public static void createDir(String path) {
		// Creating a File object
		File file = new File(path);
		// Creating the directory
		boolean bool = file.mkdir();
		if (bool) {
			System.out.println("Results directory created successfully");
		} else {
			System.out.println("Sorry couldn't create results directory. Maybe already there?");
		}
	}

	public static HashMap<Integer, ColorClass> hashMLCopy(HashMap<Integer, ColorClass> hMap) {
		HashMap<Integer, ColorClass> mapCopy = new HashMap<Integer, ColorClass>();
		for (HashMap.Entry<Integer, ColorClass> entry : hMap.entrySet())
			mapCopy.put(entry.getKey().intValue(), new ColorClass(entry.getValue()));
		return mapCopy;
	}

	public static ArrayList<Integer>[] arrayLIntCopy(ArrayList<Integer>[] aList) {
		// create a deep copy of aList
		int q = aList.length;
		ArrayList<Integer>[] newList = new ArrayList[q];
		ArrayList<Integer> listV;
		for (int i = 0; i < q; i++) {
			listV = new ArrayList<Integer>();
			if (aList[i] != null) {
				Iterator<Integer> iterV = aList[i].iterator();
				while (iterV.hasNext())
					listV.add(iterV.next().intValue());
			}
			newList[i] = listV;
		}
		return newList;
	}

	public static ArrayList<Pair> arrayLPairCopy(ArrayList<Pair> pairList) {
		// create a deep copy of pairList
		ArrayList<Pair> newPairList = new ArrayList<Pair>();
		Pair _pair;
		if (pairList != null) {
			Iterator<Pair> iterV = pairList.iterator();
			while (iterV.hasNext()) {
				_pair = iterV.next();
				newPairList.add(new Pair(_pair.from, _pair.to, _pair.fromId, _pair.toId, _pair.node));
			}
		}
		return pairList;
	}

	public static double lowerBound(double _obj) {
		double lBound = Math.floor(_obj);
		if (_obj - Math.floor(_obj) > precisionLB)
			lBound = Math.ceil(_obj);
		return lBound;
	}

	public static boolean[] characteristic(int[] clustersV, ColorClass colorClass) {
		int k = clustersV.length, i;
		boolean[] characteristic = new boolean[k];
		Iterator<Integer> iter = colorClass.vertices.iterator();
		while (iter.hasNext()) {
			i = iter.next().intValue();
			characteristic[clustersV[i]] = true;
		}
		return characteristic;
	}

	public static boolean intersect(int[] clustersV, ColorClass colorClass1, ColorClass colorClass2) {
		boolean[] characteristic1 = characteristic(clustersV, colorClass1),
				characteristic2 = characteristic(clustersV, colorClass2);
		int k = clustersV.length;
		for (int j = 0; j < k; j++)
			if (characteristic1[j] && characteristic2[j]) {
				// System.out.println("Common cluster" + j);
				return true;
			}
		return false;
	}

	public static boolean intersectsCluster(int[] clustersV, ColorClass colorClass, int jCluster) {
		int i;
		Iterator<Integer> iter = colorClass.vertices.iterator();
		while (iter.hasNext()) {
			i = iter.next().intValue();
			if (clustersV[i] == jCluster)
				return true;
		}
		return false;
	}

	public static boolean doesntIntersectClusters(int[] clustersV, boolean[] clusters, ColorClass colorClass) {
		int i;
		Iterator<Integer> iter = colorClass.vertices.iterator();
		while (iter.hasNext()) {
			i = iter.next().intValue();
			if (clusters[clustersV[i]])
				return false;
		}
		return true;
	}

	public static ArrayList<Integer> threeCycle3Clusters(RMP rmp, int jCluster) {
		HashMap<Integer, ColorClass> _colClList = rmp.colClList;
		ArrayList<Integer> listOfClasses = new ArrayList<Integer>();
		int[] clustersV = rmp.clustersV;
		int i, k = rmp.noClusters, l1, l2, l3, len;
		boolean[] commonClusters = new boolean[k], charact, charact1, charact2;
		Integer tt, ll1, ll2, ll3;
		ColorClass _colClass, _colClass1, _colClass2, _colClass3;
		Random random = new Random();

		// find two classes intersecting the cluster jCluster:
		len = rmp.clusterColCl[jCluster].size();
		if (len > 1) {
			l1 = random.nextInt(len);
			if (l1 > 0)
				l2 = random.nextInt(l1);
			else
				l2 = random.nextInt(len - 1) + 1;
			ll1 = rmp.clusterColCl[jCluster].get(l1);
			ll2 = rmp.clusterColCl[jCluster].get(l2);
			listOfClasses.add(ll1);
			listOfClasses.add(ll2);

			_colClass1 = _colClList.get(ll1);
			_colClass2 = _colClList.get(ll2);
			charact1 = characteristic(clustersV, _colClass1);
			charact2 = characteristic(clustersV, _colClass2);

			// find their common intersecting clusters:
			for (int h = 0; h < k; h++)
				if (charact1[h] == true && charact2[h] == true)
					commonClusters[h] = true;
			for (HashMap.Entry<Integer, ColorClass> entry : _colClList.entrySet()) {
				tt = entry.getKey();
				_colClass = entry.getValue();
				charact = characteristic(clustersV, _colClass);
				if (intersect(clustersV, _colClass1, _colClass) && intersect(clustersV, _colClass2, _colClass)
						&& doesntIntersectClusters(clustersV, commonClusters, _colClass)) {
					listOfClasses.add(tt);
					break;
				}
			}
		}
		return listOfClasses;
	}

	public static ArrayList<Integer> cliqueFacet(RMP rmp, int jCluster) {
		HashMap<Integer, ColorClass> _colClList = rmp.colClList;
		int[] clusterV = rmp.clustersV;
		ArrayList<Integer> listOfClasses = new ArrayList<Integer>(), startingList = new ArrayList<Integer>();
		startingList = threeCycle3Clusters(rmp, jCluster);
		ArrayList<ColorClass> _classList = new ArrayList<ColorClass>();
		ColorClass _colClass, _currentColClass;
		Integer tt;
		int t;
		boolean flag;
		if (startingList != null & startingList.size() == 3) {
			listOfClasses = startingList;
			_classList.add(rmp.colClList.get(startingList.get(0)));
			_classList.add(rmp.colClList.get(startingList.get(1)));
			_classList.add(rmp.colClList.get(startingList.get(2)));

			for (HashMap.Entry<Integer, ColorClass> entry : _colClList.entrySet()) {
				tt = entry.getKey();
				t = tt.intValue();
				if (t != startingList.get(0).intValue() && t != startingList.get(1).intValue()
						&& t != startingList.get(2).intValue()) {
					_colClass = entry.getValue();
					Iterator<ColorClass> iter = _classList.iterator();
					flag = true;
					while (iter.hasNext()) {
						_currentColClass = iter.next();
						if (!intersect(clusterV, _colClass, _currentColClass)) {
							flag = false;
							break;
						}
					}
					if (flag) {
						_classList.add(_colClass);
						listOfClasses.add(tt);
					}
				}
			}
		}
		return listOfClasses;
	}

	public static double facetsIneq(RMP rmp, int _noFacets) throws GRBException {
		rmp.model.update();
		GRBModel _model = new GRBModel(rmp.model);
		if (_noFacets > 0) {
			GRBLinExpr expr = new GRBLinExpr();
			GRBVar var;
			ArrayList<Integer> listOfClasses = new ArrayList<Integer>();
			int noOfFacets = 0, no = rmp.noClusters, t;
			Integer tt;
			long exTime_ = System.nanoTime();// , exTime_f = System.nanoTime();
			for (int h = 0; h < no; h++) {
				for (int i = 0; i < _noFacets; i++) {
					listOfClasses = cliqueFacet(rmp, h);
					if (listOfClasses != null && listOfClasses.size() > 0) {
						noOfFacets += 1;
						expr = new GRBLinExpr();
						Iterator<Integer> iter = listOfClasses.iterator();
						while (iter.hasNext()) {
							tt = iter.next();
							t = tt.intValue();
							var = _model.getVarByName("x" + t);
							expr.addTerm(1.0, var);
						}
						_model.addConstr(expr, GRB.LESS_EQUAL, 1.0, "FacetCluster_" + h + "_" + i);
						_model.update();
					}
				}
			}
			_model.optimize();
		}
		return _model.get(DoubleAttr.ObjVal);
	}

	public static GRBModel facetsIneqModel(RMP rmp, double existingOpt, int _noOfClqFacets, int _noOfMClqFacets,
			String fileName, int pbNo) throws GRBException {
		String path = "../data/PartitionCol/results/" + fileName;
		GRBModel _model = new GRBModel(rmp.model);
		GRBLinExpr expr = new GRBLinExpr();
		GRBVar var;
		ArrayList<Integer> listOfClasses = new ArrayList<Integer>();
		int noOfClqFacets = 0, noOfMClqFacets = 0, no1 = rmp.noClusters, no2 = rmp.maxClassCard, t;
		Integer tt;
		long exTime = System.nanoTime();

		if (_noOfClqFacets > 0) {
			long exTime_1 = System.nanoTime();
			for (int h = 0; h < no1; h++) {
				for (int i = 0; i < _noOfClqFacets; i++) {
					listOfClasses = cliqueFacet(rmp, h);
					if (listOfClasses != null && listOfClasses.size() > 0) {
						noOfClqFacets += 1;
						expr = new GRBLinExpr();
						Iterator<Integer> iter = listOfClasses.iterator();
						while (iter.hasNext()) {
							tt = iter.next();
							t = tt.intValue();
							var = _model.getVarByName("x" + t);
							expr.addTerm(1.0, var);
						}
						_model.addConstr(expr, GRB.LESS_EQUAL, 1.0, "FacetCliqueCluster_" + h + "_" + i);
					}
				}
			}
			_model.update();
			_model.write(path + "/model_ClqFacets_" + pbNo + ".lp");
		}
		if (no2 % 2 == 0)
			no2--;
		if (_noOfMClqFacets > 0) {
			long exTime_2 = System.nanoTime();
			for (int h = 1; h < no2 / 2; h++) {
				for (int i = 0; i < _noOfMClqFacets; i++) {
					listOfClasses = addMajorityClique(rmp, 2 * h + 1);
					if (listOfClasses != null && listOfClasses.size() > 0) {
						noOfMClqFacets += 1;
						expr = new GRBLinExpr();
						Iterator<Integer> iter = listOfClasses.iterator();
						while (iter.hasNext()) {
							tt = iter.next();
							t = tt.intValue();
							var = _model.getVarByName("x" + t);
							expr.addTerm(1.0, var);
						}
						_model.addConstr(expr, GRB.LESS_EQUAL, 1.0, "FacetMCliqueCluster_" + h + "_" + i);
					}
				}
			}
			_model.update();
			_model.write(path + "/model_MClqFacets_" + pbNo + ".lp");
		}
		if (_noOfClqFacets == 0 && _noOfMClqFacets == 0)
			return rmp.model;
		_model.optimize();
		return _model;
	}

	public static ArrayList<Integer> addMajorityClique(RMP rmp, int _xSize) throws GRBException {
		ArrayList<Integer> _listOfClasses = new ArrayList<Integer>();
		Integer tt, pp;
		int s = 0, k = rmp.noClusters;
		boolean[] charactX = createX(rmp, _xSize);
		ColorClass _colClass;
		for (HashMap.Entry<Integer, ColorClass> entry : rmp.colClList.entrySet()) {
			tt = entry.getKey();
			_colClass = entry.getValue();
			Iterator<Integer> iterCol = _colClass.vertices.iterator();
			s = 0;
			while (iterCol.hasNext()) {
				pp = iterCol.next();
				if (charactX[rmp.clustersV[pp.intValue()]])
					s++;
			}
			if (s >= (_xSize + 1) / 2)
				_listOfClasses.add(tt);
		}
		return _listOfClasses;
	}

	public static boolean[] createX(RMP rmp, int size) {
		boolean[] charactX = new boolean[k];
		Random rand = new Random();
		Object[] colClasses = rmp.colClList.values().toArray();
		int max = 100, k = 0, s = 0, len = colClasses.length;
		ColorClass colCl = (ColorClass) colClasses[rand.nextInt(len)];

		while (colCl.vertices.size() < size && k < max) {
			colCl = (ColorClass) colClasses[rand.nextInt(len)];
			k++;
		}
		if (k < max) {
			s = colCl.vertices.size();
			k = 0;
			Iterator<Integer> iterCol = colCl.vertices.iterator();
			int[] charactCol = new int[s];
			while (iterCol.hasNext()) {
				charactCol[k] = iterCol.next().intValue();
				k++;
			}
			k = 0;
			int[] perm = permute(s);
			s = 0;
			while (k < size) {
				charactX[rmp.clustersV[charactCol[perm[k]]]] = true;
				k++;
			}
		}
		return charactX;
	}

	public static ArrayList<Integer> createListArray(ArrayList<Integer> list) {
		ArrayList<Integer> newlist = new ArrayList<Integer>();
		Iterator<Integer> iterL = list.iterator();
		while (iterL.hasNext())
			newlist.add(iterL.next());
		return newlist;
	}

	public static boolean checkClassInList(ArrayList<Integer> list, HashMap<Integer, ColorClass> masterList,
			ColorClass colClass, int noVert) {
		ColorClass currentCl;
		Integer t;
		if (list != null && list.size() > 0) {
			Iterator<Integer> iterL = list.iterator();
			while (iterL.hasNext()) {
				t = iterL.next();
				if (masterList != null && masterList.size() > 0) {
					currentCl = masterList.get(t);
					if (currentCl.isEqual(colClass, noVert))
						return true;
				}
			}
		}
		return false;
	}

	public static void ShowCPCProblem(RMP rmp, int pbNo) throws GRBException {
		Integer tt;
		double val, sum;
		int t;
		ColorClass _colClass;
		String path = "../data/PartitionCol/results/";
		System.out.println("+++++++++++++++++++++++++++");
		System.out.println("No of vertices: " + rmp.noVertices + " | No of clusters: " + rmp.noClusters);
		System.out.print("Optimum for rmp: " + rmp.model.get(DoubleAttr.ObjVal) + " | No of colors: "
				+ (rmp.noClusters - rmp.model.get(DoubleAttr.ObjVal)));
		System.out.println("----------------------------------------------------------");

		for (HashMap.Entry<Integer, ColorClass> entry : rmp.colClList.entrySet()) {
			tt = entry.getKey();
			_colClass = entry.getValue(); // use key and value
			val = rmp.model.getVarByName("x" + tt.intValue()).get(GRB.DoubleAttr.X);
			if (val > 0.9) {
				System.out.println("ColClass: " + tt.intValue() + " | val = " + val);
				Iterator<Integer> iter = _colClass.vertices.iterator();
				while (iter.hasNext()) {
					t = iter.next().intValue();
					System.out.print(" " + t + "(" + rmp.clustersV[t] + ")");
				}
				// System.out.println();
				System.out.println();
				// _colClass.toString();
			}
		}
		System.out.println("+++++++++++++++++++++++++++");
	}

	public static void ShowCPCProblem(int _noVertices, int _noClusters, int[] _clustersV, GRBModel _model,
			HashMap<Integer, ColorClass> _colClList, int pbNo) throws GRBException {
		Integer tt;
		double val, sum;
		int t;
		ColorClass _colClass;
		String path = "../data/PartitionCol/results/";
		System.out.println("++++++++++++++++++++++++++++++++++++++++++++++++++++++");
		System.out.println("No of vertices: " + _noVertices + " | No of clusters: " + _noClusters);
		System.out.print("Optimum for rmp: " + _model.get(DoubleAttr.ObjVal) + " | No of colors: "
				+ (_noClusters - _model.get(DoubleAttr.ObjVal)));
		System.out.println();
		System.out.println("----------------------------------------------------------");
		for (HashMap.Entry<Integer, ColorClass> entry : _colClList.entrySet()) {
			tt = entry.getKey();
			_colClass = entry.getValue(); // use key and value
			val = _model.getVarByName("x" + tt.intValue()).get(GRB.DoubleAttr.X);
			if (val > 1 - precisionBB) {
				System.out.print("Coloring class: " + tt.intValue() + "|");
				Iterator<Integer> iter = _colClass.vertices.iterator();
				while (iter.hasNext()) {
					t = iter.next().intValue();
					System.out.print(" " + t + "(" + _clustersV[t] + ")");
				}
				System.out.println();
			}
		}
		System.out.println("++++++++++++++++++++++++++++++++++++++++++++++++++++++");
	}

	public static int[] addCD(GRBModel model, RMP rmp) throws GRBException {
		GRBVar[] vars = model.getVars();
		GRBVar var;
		String varName;
		double val;
		int i, h, hh, _nrColors = 0, s;
		int[] colors = new int[n];
		ColorClass _colorClass;
		Iterator<Integer> iter;

		for (int j = 0; j < n; j++)
			colors[j] = -2;
		for (int p = 0; p < vars.length; p++) {
			var = vars[p];
			varName = var.get(GRB.StringAttr.VarName);
			h = varName.indexOf('x');
			if (h != -1) {
				hh = Integer.valueOf(varName.substring(h + 1));
				val = var.get(GRB.DoubleAttr.X);
				if (val > 0) {
					_colorClass = rmp.colClList.get(hh);
					iter = _colorClass.vertices.iterator();
					while (iter.hasNext()) {
						i = iter.next().intValue();
						colors[i] = _nrColors;
					}
					_nrColors++;
				}
			}
		}
		for (int j = 0; j < n; j++)
			if (colors[j] >= 0) {
				s = clusters[j];
				for (int p = 0; p < n; p++)
					if (clusters[p] == s && p != j)
						colors[p] = -1;
			}
		for (int j = 0; j < n; j++)
			if (colors[j] == -2) {
				colors[j] = _nrColors;
				s = clusters[j];
				for (int p = 0; p < n; p++)
					if (clusters[p] == s && p != j)
						colors[p] = -1;
				_nrColors++;
			}
		return colors;
	}

	public static RMP buildInitialLPModelSlack(String fileName, boolean deterministic) throws GRBException {
		// build the initial LP model for the Partition Coloring Problem (PCP)
		int[] vertex = new int[n], cluster = new int[k];
		ArrayList<Integer>[] vertexCC = new ArrayList[n];
		ArrayList<Integer>[] clusterCC = new ArrayList[k];
		ArrayList<Integer>[] clusterCCClique = null;
		ArrayList<Pair> sameCV = new ArrayList<Pair>();
		ArrayList<Pair> diffCV = new ArrayList<Pair>();
		HashMap<Integer, ColorClass> colorClList = new HashMap<Integer, ColorClass>();

		int l = 0, firstClassNo = noOfCreatedClasses, _noRestoredClasses = 0;
		GRBVar var;
		GRBEnv env = new GRBEnv();
		GRBModel model = new GRBModel(env);
		GRBLinExpr expr = new GRBLinExpr(), objFunction = new GRBLinExpr();
		env.set(GRB.IntParam.OutputFlag, 0);
		model.set(GRB.IntParam.OutputFlag, 0);

		for (int i = 0; i < n; i++) {
			vertexCC[i] = new ArrayList<Integer>();
			vertex[i] = i;
		}
		for (int h = 0; h < k; h++) {
			clusterCC[h] = new ArrayList<Integer>();
			cluster[h] = h;
		}

		for (int h = 0; h < k; h++) {
			expr = new GRBLinExpr();
			var = model.addVar(0, GRB.INFINITY, 0, GRB.CONTINUOUS, "slack_" + h);
			expr.addTerm(1.0, var);
			model.addConstr(expr, GRB.EQUAL, 1.0, "cluster_" + h);
		}
		model.update();
		for (int h = 0; h < k; h++)
			objFunction.addTerm(0, model.getVarByName("slack_" + h));
		model.setObjective(objFunction);
		model.set(GRB.IntAttr.ModelSense, GRB.MAXIMIZE);
		model.update();
		_noRestoredClasses = 0;
		RMP _rmp = new RMP(model, firstClassNo, _noRestoredClasses, n, vertex, k, cluster, adjacency, clusters,
				vertexCC, clusterCC, clusterCCClique, fileName, diffCV, sameCV, colorClList, "root", 0);
		String path = "../data/PartitionCol/results/";
		_rmp.model.write(path + "/model_Initial1.lp");
		for (int i = 0; i < noStages; i++) {
			addClassesPopulate(_rmp, oneStepCDRandom(_rmp, deterministic));
		}
		return _rmp;
	}

	public static RMP buildLPModelPairContraction(RMP rmp, Pair pair, String fileName, int pbNo) throws GRBException {
		HashMap<Integer, ColorClass> _colClList = new HashMap<Integer, ColorClass>(),
				_cClist = hashMLCopy(rmp.colClList);
		ArrayList<Integer>[] _clusterCCClique = rmp.clusterColClClq;// TODO: or null?
		ArrayList<Pair> _sameCV = arrayLPairCopy(rmp.sameColNodes), _diffCV = arrayLPairCopy(rmp.diffColNodes);
		int h, uId = pair.fromId, vId = pair.toId, _noVertices, _noClusters, _firstClassNo = noOfCreatedClasses,
				_noRestoredClasses = 0, p = -1, t, cl_u, cl_v, cl_uOrv_card = 0, _maxClassCard = 0;
		Integer tt, pp;
		boolean _isANewClass;
		boolean[] cluster_u_Or_v = new boolean[rmp.noVertices];
		ColorClass _colClass, _newClass, _newClass_1, _newClass_2;

		cl_u = rmp.clustersV[uId];// the true cluster id
		cl_v = rmp.clustersV[vId];// the true cluster id
		for (int i = 0; i < rmp.noVertices; i++)
			if (rmp.clustersV[i] == cl_u || rmp.clustersV[i] == cl_v) {
				cluster_u_Or_v[i] = true;
				cl_uOrv_card++;
			}
		_noVertices = rmp.noVertices - cl_uOrv_card + 1;
		_noClusters = rmp.noClusters - 1;

		int[] _vertex = new int[_noVertices];
		int[] _cluster = new int[_noClusters];
		int[] _clustersV = new int[_noVertices];
		int[] _vertexOlderInd = new int[_noVertices];
		int[] _inverseVertexOlderInd = new int[rmp.noVertices];
		ArrayList<Integer>[] _vertexCC = arrayLIntCopy(rmp.vertexColCl), _vertexColCl = new ArrayList[_noVertices];
		ArrayList<Integer>[] _clusterCC = arrayLIntCopy(rmp.clusterColCl), _clusterColCl = new ArrayList[_noVertices];

		for (int i = 0; i < _noVertices; i++)
			_vertexColCl[i] = new ArrayList<Integer>();
		for (int hh = 0; hh < _noClusters; hh++)
			_clusterColCl[hh] = new ArrayList<Integer>();

		h = t = 0;
		while (t < rmp.noVertices) {
			while (t < rmp.noVertices && !cluster_u_Or_v[t]) {
				_vertex[h] = rmp.vertex[t];
				_vertexOlderInd[h] = t;
				_inverseVertexOlderInd[t] = h;
				if (rmp.clustersV[t] < cl_u && rmp.clustersV[t] < cl_v)
					_clustersV[h] = rmp.clustersV[t];
				if (rmp.clustersV[t] > cl_u && rmp.clustersV[t] > cl_v)
					_clustersV[h] = rmp.clustersV[t] - 2;
				if ((rmp.clustersV[t] > cl_u && rmp.clustersV[t] < cl_v)
						|| (rmp.clustersV[t] < cl_u && rmp.clustersV[t] > cl_v))// TODO:?!
					_clustersV[h] = rmp.clustersV[t] - 1;
				h++;
				t++;
			}
			t++;
		}
		noOfCreatedVertices++;
		noOfCreatedClusters++;
		_vertex[_noVertices - 1] = noOfCreatedVertices;// this the new vertex
		_clustersV[_noVertices - 1] = _noClusters - 1;// this is the new cluster
		pair.node = noOfCreatedVertices;
		_sameCV.add(pair);
		boolean[][] _adjacencyM = new boolean[_noVertices][_noVertices];
		for (int i = 0; i < _noVertices - 1; i++) {
			if (rmp.adjacencyM[_vertexOlderInd[i]][uId] || rmp.adjacencyM[_vertexOlderInd[i]][vId]) {
				_adjacencyM[i][_noVertices - 1] = true;
				_adjacencyM[_noVertices - 1][i] = true;
			}
			for (int j = 0; j < _noVertices - 1; j++)
				if (i != j)
					_adjacencyM[i][j] = rmp.adjacencyM[_vertexOlderInd[i]][_vertexOlderInd[j]];
		}
		// traverse the color classes containing u:
		if (_vertexCC[uId] != null && _vertexCC[uId].size() > 0) {
			Iterator<Integer> itColClass_uIdIterator = _vertexCC[uId].iterator();
			while (itColClass_uIdIterator.hasNext()) {
				tt = itColClass_uIdIterator.next().intValue();
				itColClass_uIdIterator.remove();// remove (using the iterator) the color class from the list of u
				_colClass = _cClist.remove(tt);
				if (_vertexCC[vId].contains(tt)) {// the color class contains v also
					// TODO: just verify if _colClass contains vId
					_vertexCC[vId].remove(tt);
					if (_colClass.vertices.size() > 2) {// the color class contains more than u and v
						_newClass = new ColorClass();// create the new color class
						_colClass.vertices.remove((Integer) uId);
						_colClass.vertices.remove((Integer) vId);
						Iterator<Integer> iterColCl = _colClass.vertices.iterator();
						// build the new color class:
						while (iterColCl.hasNext()) {
							pp = iterColCl.next();
							p = pp.intValue();
							// remove the old color class in order to avoid processing it twice:
							_vertexCC[p].remove(tt);
							_newClass.vertices.add((Integer) _inverseVertexOlderInd[p]);
						}
						_newClass.vertices.add((Integer) _noVertices - 1);// add the new vertex
						iterColCl = _newClass.vertices.iterator();
						// add the new color class to the vertices lists and to the clusters lists:
						while (iterColCl.hasNext()) {
							p = iterColCl.next().intValue();
							_vertexColCl[p].add(tt);
							_clusterColCl[_clustersV[p]].add(tt);
						}
						// add the new color class to the master list:
						_colClList.put(tt, _newClass);
						if (_newClass.vertices.size() > _maxClassCard)
							_maxClassCard = _newClass.vertices.size();
						_noRestoredClasses++;
					}
				} else {// the color class doesn't contain v
					if (_colClass.vertices.size() >= 2) {// the color class contains more than u
						_newClass = new ColorClass();// create the new color class
						_isANewClass = false;
						_colClass.vertices.remove((Integer) uId);
						Iterator<Integer> iterColCl = _colClass.vertices.iterator();
						// build the new color class:
						while (iterColCl.hasNext()) {
							pp = iterColCl.next();
							p = pp.intValue();
							// remove the old color class in order to avoid processing it twice:
							_vertexCC[p].remove(tt);
							// if p is not adjacent with v nor is contained in the same cluster with v, then
							// p should be kept in the new color class:
							if (!rmp.adjacencyM[p][vId] && rmp.clustersV[p] != rmp.clustersV[vId])
								_newClass.vertices.add((Integer) _inverseVertexOlderInd[p]);
						}
						// the new color class will be added iff contains at least one vertex,
						// besides the new vertex.
						if (_newClass != null && _newClass.vertices != null & _newClass.vertices.size() > 0) {
							_newClass.vertices.add((Integer) _noVertices - 1);// add the new vertex
							iterColCl = _newClass.vertices.iterator();
							if (!checkClassInList(_vertexColCl[_noVertices - 1], _colClList, _newClass, _noVertices)) {
								// add the new color class to the vertices lists and to the clusters lists:
								while (iterColCl.hasNext()) {
									p = iterColCl.next().intValue();
									_vertexColCl[p].add(tt);
									_clusterColCl[_clustersV[p]].add(tt);
								}
								// add the new color class to the master list:
								_colClList.put(tt, _newClass);
								if (_newClass.vertices.size() > _maxClassCard)
									_maxClassCard = _newClass.vertices.size();
								_noRestoredClasses++;
							}
						}
					}
				}
			}
		}
		// traverse the color classes containing v:
		if (_vertexCC[vId] != null && _vertexCC[vId].size() > 0) {
			Iterator<Integer> itColClass_vIdIterator = _vertexCC[vId].iterator();
			while (itColClass_vIdIterator.hasNext()) {
				tt = itColClass_vIdIterator.next().intValue();
				itColClass_vIdIterator.remove();// remove (using the iterator) the color class from the list of v
				_colClass = _cClist.remove(tt);
				// we are sure that the color class doesn't contain u - since we already
				// removed all the classes containing both u and v
				if (_colClass.vertices.size() >= 2) { // the color class contains more than v
					_newClass = new ColorClass();// create the new color class
					_isANewClass = false;
					_colClass.vertices.remove((Integer) vId);
					Iterator<Integer> iterColCl = _colClass.vertices.iterator();

					// build the new color class:
					while (iterColCl.hasNext()) {
						pp = iterColCl.next();
						p = pp.intValue();
						// remove the old color class in order to avoid processing it twice:
						_vertexCC[p].remove(tt);
						// if p is not adjacent with u nor is contained in the same cluster with u, then
						// p should be kept in the new color class:
						if (!rmp.adjacencyM[p][uId] && rmp.clustersV[p] != rmp.clustersV[uId])
							_newClass.vertices.add((Integer) _inverseVertexOlderInd[p]);
					}
					// the new color class will be added iff contains at least one vertex,
					// besides the new vertex.
					if (_newClass != null && _newClass.vertices != null & _newClass.vertices.size() > 0) {
						_newClass.vertices.add((Integer) _noVertices - 1);// add the new vertex
						iterColCl = _newClass.vertices.iterator();
						if (!checkClassInList(_vertexColCl[_noVertices - 1], _colClList, _newClass, _noVertices)) {
							// add the new color class to the vertices lists and to the clusters lists:
							while (iterColCl.hasNext()) {
								p = iterColCl.next().intValue();
								_vertexColCl[p].add(tt);
								_clusterColCl[_clustersV[p]].add(tt);
							}
							// add the new color class to the master list:
							_colClList.put(tt, _newClass);
							if (_newClass.vertices.size() > _maxClassCard)
								_maxClassCard = _newClass.vertices.size();
							_noRestoredClasses++;
						}
					}
				}
			}
		}
		// traverse all the remaining vertices lists (containing color classes)
		for (int id = 0; id < rmp.noVertices; id++) {
			if (_vertexCC[id] != null && _vertexCC[id].size() > 0) {
				Iterator<Integer> itColClass_IdIterator = _vertexCC[id].iterator();
				while (itColClass_IdIterator.hasNext()) {
					tt = itColClass_IdIterator.next().intValue();
					itColClass_IdIterator.remove();// remove (using the iterator) the color class from the list of id
					_colClass = _cClist.remove(tt);
					if (_colClass != null && _colClass.vertices.size() > 0) {
						_newClass = new ColorClass();// create the new color class
						Iterator<Integer> iterColCl = _colClass.vertices.iterator();
						// build the new color class:
						while (iterColCl.hasNext()) {
							pp = iterColCl.next();
							p = pp.intValue();
							// remove the old color class in order to avoid processing it twice:
							_vertexCC[p].remove(tt);
							if (rmp.clustersV[p] != rmp.clustersV[uId] && rmp.clustersV[p] != rmp.clustersV[vId]) {
								_newClass.vertices.add((Integer) _inverseVertexOlderInd[p]);
								// System.out.println("u, v cluster detected: " + _inverseVertexOlderInd[p]);
							}
						}
						// the new color class will be added iff contains at least two vertices
						if (_newClass != null && _newClass.vertices != null & _newClass.vertices.size() >= 2) {
							iterColCl = _newClass.vertices.iterator();
							_isANewClass = true;
							while (iterColCl.hasNext())
								if (checkClassInList(_vertexColCl[iterColCl.next().intValue()], _colClList, _newClass,
										_noVertices))
									_isANewClass = false;
							if (_isANewClass) {
								iterColCl = _newClass.vertices.iterator();
								// add the new color class to the vertices lists and to the clusters lists:
								while (iterColCl.hasNext()) {
									p = iterColCl.next().intValue();
									_vertexColCl[p].add(tt);
									_clusterColCl[_clustersV[p]].add(tt);
								}
								// add the new color class to the master list:
								_colClList.put(tt, _newClass);
								if (_newClass.vertices.size() > _maxClassCard)
									_maxClassCard = _newClass.vertices.size();
								_noRestoredClasses++;
							}
						}
					}
				}
			}
		}

		// Build the model:
		GRBEnv env = new GRBEnv();
		GRBModel _model = new GRBModel(env);
		GRBVar var;
		GRBLinExpr expr = new GRBLinExpr(), objFunction = new GRBLinExpr();
		env.set(GRB.IntParam.OutputFlag, 0);
		_model.set(GRB.IntParam.OutputFlag, 0);

		for (int j = 0; j < _noClusters; j++) {
			expr = new GRBLinExpr();
			var = _model.addVar(0, GRB.INFINITY, 0, GRB.CONTINUOUS, "slack_" + j);
			expr.addTerm(1.0, var);
			_model.update();
			// add the remaining variables from the clusters lists:
			Iterator<Integer> iterClusterColCl = _clusterColCl[j].iterator();
			while (iterClusterColCl.hasNext()) {
				tt = iterClusterColCl.next();
				t = tt.intValue();
				p = _colClList.get(tt).vertices.size();

				if (_model.getVarByName("x" + t) == null)
					var = _model.addVar(0, GRB.INFINITY, 0, GRB.CONTINUOUS, "x" + t);
				else
					var = _model.getVarByName("x" + t);
				expr.addTerm(1.0, var);
			}
			_model.addConstr(expr, GRB.EQUAL, 1.0, "cluster_" + j);
			_model.update();
		}

		for (HashMap.Entry<Integer, ColorClass> entry : _colClList.entrySet()) {
			tt = entry.getKey();
			_colClass = entry.getValue(); // use key and value
			objFunction.addTerm(_colClass.vertices.size() - 1, _model.getVarByName("x" + tt.intValue()));
		}
		_model.setObjective(objFunction);
		_model.set(GRB.IntAttr.ModelSense, GRB.MAXIMIZE);
		_model.update();

		RMP _rmp = new RMP(_model, _firstClassNo, _noRestoredClasses, _noVertices, _vertex, _noClusters, _cluster,
				_adjacencyM, _clustersV, _vertexColCl, _clusterColCl, _clusterCCClique, fileName, _diffCV, _sameCV,
				_colClList, "contraction", _maxClassCard);

		return _rmp;
	}

	public static RMP buildLPModelPairAddEdge(RMP rmp, Pair pair, String fileName) throws GRBException {
		// build the initial LP model for the Partition Coloring Problem (PCP)
		HashMap<Integer, ColorClass> _colClList = new HashMap<Integer, ColorClass>(),
				_cClist = hashMLCopy(rmp.colClList);
		ArrayList<Integer>[] _clusterCCClique = rmp.clusterColClClq;// TODO: or null?
		ArrayList<Pair> _sameCV = arrayLPairCopy(rmp.sameColNodes), _diffCV = arrayLPairCopy(rmp.diffColNodes);

		int h, uId = pair.fromId, vId = pair.toId, _noVertices = rmp.noVertices, _noClusters = rmp.noClusters,
				_firstClassNo = noOfCreatedClasses, _noRestoredClasses = 0, p = -1, t, _maxClassCard = 0;
		Integer tt, pp;
		ColorClass _colClass, _newClass, _newClass_1, _newClass_2;
		int[] _vertex = new int[_noVertices];
		int[] _cluster = new int[_noClusters];
		int[] _clustersV = new int[_noVertices];
		ArrayList<Integer>[] _vertexCC = arrayLIntCopy(rmp.vertexColCl), _vertexColCl = new ArrayList[_noVertices];
		ArrayList<Integer>[] _clusterCC = arrayLIntCopy(rmp.clusterColCl), _clusterColCl = new ArrayList[_noVertices];

		for (int i = 0; i < _noVertices; i++)
			_vertexColCl[i] = new ArrayList<Integer>();
		for (int hh = 0; hh < _noClusters; hh++)
			_clusterColCl[hh] = new ArrayList<Integer>();

		System.arraycopy(rmp.vertex, 0, _vertex, 0, _noVertices);
		System.arraycopy(rmp.clustersV, 0, _clustersV, 0, _noVertices);
		System.arraycopy(rmp.cluster, 0, _cluster, 0, _noClusters);
		boolean[][] _adjacencyM = new boolean[_noVertices][_noVertices];

		for (int i = 0; i < _noVertices; i++)
			for (int j = 0; j < _noVertices; j++)
				_adjacencyM[i][j] = rmp.adjacencyM[i][j];
		_adjacencyM[uId][vId] = true;
		_adjacencyM[vId][uId] = true;

		_diffCV.add(new Pair(pair.from, pair.to, pair.fromId, pair.toId, -1));

		// traverse the color classes containing u:
		if (_vertexCC[uId] != null && _vertexCC[uId].size() > 0) {
			Iterator<Integer> itColClass_uIdIterator = _vertexCC[uId].iterator();
			while (itColClass_uIdIterator.hasNext()) {
				tt = itColClass_uIdIterator.next().intValue();
				if (_vertexCC[vId].contains(tt)) {// the color class contains v also
					// TODO: just verify if _colClass contains vId
					_vertexCC[vId].remove(tt);
					itColClass_uIdIterator.remove();// remove (using the iterator) the color class from the list of u
					_colClass = _cClist.remove(tt);
					if (_colClass.vertices.size() > 3) {// the color class contains at least 4 vertices
						_colClass.vertices.remove((Integer) uId);
						_colClass.vertices.remove((Integer) vId);
						// create the new color classes:
						_newClass = new ColorClass();
						_newClass_1 = new ColorClass();
						_newClass_2 = new ColorClass();

						Iterator<Integer> iterColCl = _colClass.vertices.iterator();

						// build the new color classes:
						while (iterColCl.hasNext()) {
							pp = iterColCl.next();
							p = pp.intValue();
							// remove the old color class in order to avoid processing it twice:
							_vertexCC[p].remove(tt);
							_newClass.vertices.add(pp);
							_newClass_1.vertices.add(pp);
							_newClass_2.vertices.add(pp);
						}
						_newClass_1.vertices.add((Integer) uId);// add u
						_newClass_2.vertices.add((Integer) vId);// add v

						// p is the id of a vertex in _newClass
						if (!checkClassInList(_vertexCC[p], _cClist, _newClass, _noVertices)
								&& !checkClassInList(_vertexColCl[p], _colClList, _newClass, _noVertices)) {
							iterColCl = _newClass.vertices.iterator();
							// add the new color class to the vertices lists and to the clusters lists:
							while (iterColCl.hasNext()) {
								p = iterColCl.next().intValue();
								_vertexColCl[p].add(noOfCreatedClasses);
								_clusterColCl[_clustersV[p]].add(noOfCreatedClasses);
							}
							_colClList.put(noOfCreatedClasses, _newClass);
							if (_newClass.vertices.size() > _maxClassCard)
								_maxClassCard = _newClass.vertices.size();
							noOfCreatedClasses++;
							_noRestoredClasses++;
						}

						if (!checkClassInList(_vertexCC[uId], _cClist, _newClass_1, _noVertices)
								&& !checkClassInList(_vertexColCl[uId], _colClList, _newClass_1, _noVertices)) {
							iterColCl = _newClass_1.vertices.iterator();
							// add the new color class to the vertices lists and to the clusters lists:
							while (iterColCl.hasNext()) {
								p = iterColCl.next().intValue();
								_vertexColCl[p].add(noOfCreatedClasses);
								_clusterColCl[_clustersV[p]].add(noOfCreatedClasses);
							}
							_colClList.put(noOfCreatedClasses, _newClass_1);
							if (_newClass.vertices.size() > _maxClassCard)
								_maxClassCard = _newClass.vertices.size();
							noOfCreatedClasses++;
							_noRestoredClasses++;
						}

						if (!checkClassInList(_vertexCC[vId], _cClist, _newClass_2, _noVertices)
								&& !checkClassInList(_vertexColCl[vId], _colClList, _newClass_2, _noVertices)) {
							iterColCl = _newClass_2.vertices.iterator();
							// add the new color class to the vertices lists and to the clusters lists:
							while (iterColCl.hasNext()) {
								p = iterColCl.next().intValue();
								_vertexColCl[p].add(noOfCreatedClasses);
								_clusterColCl[_clustersV[p]].add(noOfCreatedClasses);
							}
							_colClList.put(noOfCreatedClasses, _newClass_2);
							if (_newClass.vertices.size() > _maxClassCard)
								_maxClassCard = _newClass.vertices.size();
							noOfCreatedClasses++;
							_noRestoredClasses++;
						}
					}

					if (_colClass.vertices.size() == 3) {// the color class contains exactly 3 vertices
						_colClass.vertices.remove((Integer) uId);
						_colClass.vertices.remove((Integer) vId);
						// create the new color classes:
						_newClass_1 = new ColorClass();
						_newClass_2 = new ColorClass();

						Iterator<Integer> iterColCl = _colClass.vertices.iterator();

						// build the new color classes:
						while (iterColCl.hasNext()) {
							pp = iterColCl.next();
							p = pp.intValue();
							// remove the old color class in order to avoid processing it twice:
							_vertexCC[p].remove(tt);
							_newClass_1.vertices.add((Integer) p);
							_newClass_2.vertices.add((Integer) p);
						}
						_newClass_1.vertices.add((Integer) uId);// add u
						_newClass_2.vertices.add((Integer) vId);// add v

						if (!checkClassInList(_vertexCC[uId], _cClist, _newClass_1, _noVertices)
								&& !checkClassInList(_vertexColCl[uId], _colClList, _newClass_1, _noVertices)) {
							iterColCl = _newClass_1.vertices.iterator();
							// add the new color class to the vertices lists and to the clusters lists:
							while (iterColCl.hasNext()) {
								p = iterColCl.next().intValue();
								_vertexColCl[p].add(noOfCreatedClasses);
								_clusterColCl[_clustersV[p]].add(noOfCreatedClasses);
							}
							_colClList.put(noOfCreatedClasses, _newClass_1);
							if (_newClass_1.vertices.size() > _maxClassCard)
								_maxClassCard = _newClass_1.vertices.size();
							noOfCreatedClasses++;
							_noRestoredClasses++;
						}

						if (!checkClassInList(_vertexCC[vId], _cClist, _newClass_2, _noVertices)
								&& !checkClassInList(_vertexColCl[vId], _colClList, _newClass_2, _noVertices)) {
							iterColCl = _newClass_2.vertices.iterator();
							// add the new color class to the vertices lists and to the clusters lists:
							while (iterColCl.hasNext()) {
								p = iterColCl.next().intValue();
								_vertexColCl[p].add(noOfCreatedClasses);
								_clusterColCl[_clustersV[p]].add(noOfCreatedClasses);
							}
							_colClList.put(noOfCreatedClasses, _newClass_2);
							if (_newClass_2.vertices.size() > _maxClassCard)
								_maxClassCard = _newClass_2.vertices.size();
							noOfCreatedClasses++;
							_noRestoredClasses++;
						}
					}
				}
			}
		}

		// traverse all the remaining variables/color classes:
		for (HashMap.Entry<Integer, ColorClass> entry : _cClist.entrySet()) {
			tt = entry.getKey();
			_colClass = entry.getValue();
			if (_colClass != null && _colClass.vertices.size() > 0) {
				_colClList.put(tt, _colClass);
				if (_colClass.vertices.size() > _maxClassCard)
					_maxClassCard = _colClass.vertices.size();
				Iterator<Integer> iterColCl = _colClass.vertices.iterator();
				while (iterColCl.hasNext()) {
					pp = iterColCl.next();
					p = pp.intValue();
					_vertexColCl[p].add(tt);
					_clusterColCl[_clustersV[p]].add(tt);
				}
			}
		}

		// Build the model:
		GRBEnv env = new GRBEnv();
		GRBModel _model = createModel(_noClusters, _clusterColCl, _colClList);
		RMP _rmp = new RMP(_model, _firstClassNo, _noRestoredClasses, _noVertices, _vertex, _noClusters, _cluster,
				_adjacencyM, _clustersV, _vertexColCl, _clusterColCl, _clusterCCClique, fileName, _diffCV, _sameCV,
				_colClList, "edge-adding", _maxClassCard);

		return _rmp;
	}

	public static GRBModel createModel(int _noClusters, ArrayList<Integer>[] _clusterColCl,
			HashMap<Integer, ColorClass> _colClList) throws GRBException {
		Integer tt;
		int t, p;
		ColorClass _colClass;
		// Build the model:
		GRBEnv env = new GRBEnv();
		GRBModel _model = new GRBModel(env);
		GRBVar var;
		GRBLinExpr expr = new GRBLinExpr(), objFunction = new GRBLinExpr();
		env.set(GRB.IntParam.OutputFlag, 0);
		_model.set(GRB.IntParam.OutputFlag, 0);
		String path = "../data/PartitionCol/results/";

		for (int j = 0; j < _noClusters; j++) {
			expr = new GRBLinExpr();
			var = _model.addVar(0, GRB.INFINITY, 0, GRB.CONTINUOUS, "slack_" + j);
			expr.addTerm(1.0, var);
			_model.update();
			// add the remaining variables from the clusters lists:
			Iterator<Integer> iterClusterColCl = _clusterColCl[j].iterator();
			while (iterClusterColCl.hasNext()) {
				tt = iterClusterColCl.next();
				t = tt.intValue();
				p = _colClList.get(tt).vertices.size();
				if (_model.getVarByName("x" + t) == null)
					var = _model.addVar(0, GRB.INFINITY, 0, GRB.CONTINUOUS, "x" + t);
				else
					var = _model.getVarByName("x" + t);
				expr.addTerm(1.0, var);
			}
			_model.addConstr(expr, GRB.EQUAL, 1.0, "cluster_" + j);
			_model.update();
		}

		_model.write(path + "/model_b.lp");

		for (HashMap.Entry<Integer, ColorClass> entry : _colClList.entrySet()) {
			tt = entry.getKey();
			_colClass = entry.getValue();
			if (_colClass == null)
				System.out.println("null class");
			objFunction.addTerm(_colClass.vertices.size() - 1, _model.getVarByName("x" + tt.intValue()));
		}
		_model.setObjective(objFunction);
		_model.set(GRB.IntAttr.ModelSense, GRB.MAXIMIZE);
		_model.update();

		_model.write(path + "/model_a.lp");

		return _model;
	}

	public static int[] oneStepCD() {
		// One step color (saturation) degree
		int colored = 0, min, vertex, max, cluster, color;
		boolean[] clusterColored = new boolean[k];
		int[] _colored = new int[n], _colorDegree = new int[n], _coloredX = new int[k], _degreeX = new int[k];
		for (int i = 0; i < n; i++)
			_colored[i] = -1;

		while (colored < k) {
			for (int h = 0; h < k; h++)
				_coloredX[h] = -1;

			// compute X:
			for (int h = 0; h < k; h++)
				if (!clusterColored[h]) {
					min = n + 1;
					vertex = -1;
					for (int i = 0; i < n; i++)
						if (clusters[i] == h && _colorDegree[i] < min) {
							vertex = i;
							min = _colorDegree[i];
						}
					if (vertex != -1) {
						_coloredX[h] = vertex;
						_degreeX[h] = min;
					}
				}

			// find the maximum color degree vertex from X
			max = -1;
			cluster = -1;
			vertex = -1;
			for (int h = 0; h < k; h++)
				if (_coloredX[h] != -1 && _degreeX[h] > max) {
					cluster = h;
					vertex = _coloredX[h];
					max = _degreeX[h];
				}
			if (cluster != -1)
				clusterColored[cluster] = true;

			// color this vertex with the smallest available color
			color = 0;
			for (int h = 0; h < k; h++)
				_coloredX[h] = -1;
			for (int i = 0; i < n; i++)
				if (adjacency[i][vertex] && _colored[i] != -1) {
					_coloredX[_colored[i]] = 1;
				}
			for (int h = 0; h < k; h++)
				if (_coloredX[h] == -1) {
					color = h;
					_colored[vertex] = h;
					break;
				}
			colored++;
			// update the color (saturation) degree for the neighbors of the vertex
			for (int i = 0; i < n; i++) {
				if (adjacency[i][vertex] && !clusterColored[clusters[i]] && clusters[i] != clusters[vertex]
						&& _colored[i] == -1) {
					boolean flag = false;
					for (int j = 0; j < n; j++)
						if (!flag && adjacency[i][j] && j != vertex && clusterColored[clusters[j]]
								&& clusters[i] != clusters[j] && _colored[i] == color) {
							flag = true;
							break;
						}
					if (!flag)
						_colorDegree[i]++;
				}
			}
		}

		int _max = 0;
		for (int l = 0; l < _colored.length; l++)
			if (_colored[l] > _max)
				_max = _colored[l];
		return _colored;
	}

	public static int[] oneStepCDNew() {
		// One step color (saturation) degree
		int colored = 0, min, vertex, max, cluster, color;
		boolean[] clusterColored = new boolean[k];
		int[] _colored = new int[n], _colorDegree = new int[n], _coloredX = new int[k], _degreeX = new int[k];
		for (int i = 0; i < n; i++)
			_colored[i] = -1;

		while (colored < k) {
			for (int h = 0; h < k; h++)
				_coloredX[h] = -1;

			// compute X:
			for (int h = 0; h < k; h++)
				if (!clusterColored[h]) {
					min = n + 1;
					vertex = -1;
					for (int i = 0; i < n; i++)
						if (clusters[i] == h && _colorDegree[i] < min) {
							vertex = i;
							min = _colorDegree[i];
						}
					if (vertex != -1) {
						_coloredX[h] = vertex;
						_degreeX[h] = min;
					}
				}

			// find the maximum color degree vertex from X
			max = -1;
			cluster = -1;
			vertex = -1;
			for (int h = 0; h < k; h++)
				if (_coloredX[h] != -1 && _degreeX[h] > max) {
					cluster = h;
					vertex = _coloredX[h];
					max = _degreeX[h];
				}
			if (cluster != -1)
				clusterColored[cluster] = true;

			// color this vertex with the smallest available color
			color = 0;
			for (int h = 0; h < k; h++)
				_coloredX[h] = -1;
			for (int i = 0; i < n; i++)
				if (adjacency[i][vertex] && _colored[i] != -1) {
					_coloredX[_colored[i]] = 1;// mark the used colors
				}
			for (int h = 0; h < k; h++)
				if (_coloredX[h] == -1) {
					color = h;
					_colored[vertex] = h;
					break;
				}
			colored++;
			// update the color (saturation) degree for the neighbors of the vertex
			for (int i = 0; i < n; i++) {
				if (_colored[i] == -1 && !clusterColored[clusters[i]] && adjacency[i][vertex]) {
					boolean flag = false;
					for (int j = 0; j < n; j++)
						if (_colored[j] == color && adjacency[i][j] && j != vertex) {
							flag = true;
							break;
						}
					if (!flag)
						_colorDegree[i]++;
				}
			}
		}

		int _max = 0;
		for (int l = 0; l < n; l++)
			if (_colored[l] > _max)
				_max = _colored[l];
		return _colored;
	}

	public static int[] oneStepCDRandom(RMP rmp, boolean deterministic) {
		// One step color (saturation) degree
		int colored = 0, min, vertex, max, cluster, color, n = rmp.noVertices, k = rmp.noClusters;
		int[] clusters = rmp.clustersV;
		boolean[][] adjacency = rmp.adjacencyM;
		boolean[] clusterColored = new boolean[k];
		int[] _colored = new int[n], _colorDegree = new int[n], _coloredX = new int[k], _degreeX = new int[k],
				node = new int[n], clust = new int[k];
		if (!deterministic) {
			node = permute(n);
			clust = permute(k);
		} else {
			for (int i = 0; i < n; i++)
				node[i] = i;
			for (int j = 0; j < k; j++)
				clust[j] = j;
		}
		for (int i = 0; i < n; i++)
			_colored[i] = -1;
		// Collections.shuffle(Arrays.asList(_colored));
		while (colored < k) {
			for (int h = 0; h < k; h++)
				_coloredX[h] = -1;
			// compute X:
			for (int h = 0; h < k; h++)
				if (!clusterColored[clust[h]]) {
					min = n + 1;
					vertex = -1;
					for (int i = 0; i < n; i++)
						if (clust[clusters[node[i]]] == clust[h] && _colorDegree[node[i]] < min) {
							vertex = node[i];
							min = _colorDegree[node[i]];
						}
					if (vertex != -1) {
						_coloredX[clust[h]] = vertex;
						_degreeX[clust[h]] = min;
					}
				}

			// find the maximum color degree vertex from X
			max = -1;
			cluster = -1;
			vertex = -1;
			for (int h = 0; h < k; h++)
				if (_coloredX[clust[h]] != -1 && _degreeX[clust[h]] > max) {
					cluster = clust[h];
					vertex = _coloredX[clust[h]];
					max = _degreeX[clust[h]];
				}
			if (cluster != -1)
				clusterColored[cluster] = true;

			// color this vertex with the smallest available color; _coloredX[h]=1 means the
			// color h is used.
			color = 0;
			for (int h = 0; h < k; h++)
				_coloredX[h] = -1;
			for (int i = 0; i < n; i++) {
				// System.out.println("node[" + i + "] = " + node[i] + ", vertex= " + vertex);
				if (adjacency[node[i]][vertex] && _colored[node[i]] != -1)
					_coloredX[_colored[node[i]]] = 1;// mark the used colors
			}
			for (int h = 0; h < k; h++)
				if (_coloredX[h] == -1) {
					color = h;
					_colored[vertex] = h;
					break;
				}
			colored++;
			// update the color (saturation) degree for the neighbors of the vertex
			for (int i = 0; i < n; i++) {
				if (_colored[node[i]] == -1 && !clusterColored[clust[clusters[node[i]]]]
						&& adjacency[node[i]][vertex]) {
					boolean flag = false;
					for (int j = 0; j < n; j++)
						if (_colored[node[j]] == color && adjacency[node[i]][node[j]] && node[j] != vertex) {
							flag = true;
							break;
						}
					if (!flag)
						_colorDegree[node[i]]++;
				}
			}
		}

		int _max = -1;
		for (int l = 0; l < n; l++)
			if (_colored[l] > _max)
				_max = _colored[l];
		return _colored;
	}

	public static int[] permute(int n) {
		int aux, p;
		int[] a = new int[n];

		for (int i = 0; i < n; i++)
			a[i] = i;
		for (int i = 0; i < n; i++) {
			p = (int) (Math.random() * (i + 1));
			aux = a[p];
			a[p] = a[i];
			a[i] = aux;
		}
		return a;
	}

	public static boolean checkStableSet(RMP rmp, boolean characteristic[]) {
		int n = characteristic.length;
		for (int i = 0; i < n; i++)
			if (characteristic[i])
				for (int j = i; j < n; j++) {
					if (characteristic[j] && rmp.adjacencyM[i][j])
						return false;
				}
		return true;
	}

	public static boolean isStable(int[] clustersV, boolean[][] adjacency, ColorClass colClass, int v) {
		// using a coloring class
		int i;
		Iterator<Integer> iter = colClass.vertices.iterator();

		while (iter.hasNext()) {
			i = iter.next().intValue();
			if (adjacency[i][v] || (clustersV[i] == clustersV[v]))
				return false;
		}
		return true;
	}

	public static boolean checkStableSet(RMP rmp, ColorClass newClass) {

		boolean[] characteristic = new boolean[rmp.noVertices];
		int i;
		Iterator<Integer> iter = newClass.vertices.iterator();
		while (iter.hasNext()) {
			i = iter.next().intValue();
			characteristic[i] = true;
		}
		return checkStableSet(rmp, characteristic);
	}

	public static boolean isStable(int[] clustersV, boolean[][] adjacency, boolean[] charColClass, int v) {
		// using a characteristic vector
		int n = charColClass.length;
		for (int i = 0; i < n; i++)
			if ((charColClass[i] && adjacency[i][v]) || (charColClass[i] && (clustersV[i] == clustersV[v])))
				return false;
		return true;
	}

	public static ArrayList<Integer> buildInitialHSet(int[] clustersV, boolean[][] adjacency, boolean[] charColClass,
			int n, int u) {
		ArrayList<Integer> hSet = new ArrayList<Integer>();

		for (int j = 0; j < n; j++)
			if (!charColClass[j] && j != u && isStable(clustersV, adjacency, charColClass, j))
				hSet.add((Integer) j);
		return hSet;
	}

	public static ArrayList<Integer> buildHSet(int[] clustersV, boolean[][] adjacency, boolean[] charColClass,
			ArrayList<Integer> hSet, int n) {
		// using a coloring class
		ArrayList<Integer> deltaSet = new ArrayList<Integer>();
		Iterator<Integer> iter = hSet.iterator();
		int i;
		boolean[] charSet = new boolean[n];

		while (iter.hasNext()) {
			i = iter.next().intValue();
			charSet[i] = true;
		}

		for (int j = 0; j < n; j++)
			if (charSet[j] && isStable(clustersV, adjacency, charColClass, j))
				deltaSet.add((Integer) j);
		return deltaSet;
	}

	public static boolean[] characteristicV(ColorClass colClass, int n) {
		boolean[] _characteristicV = new boolean[n];
		Iterator<Integer> iter = colClass.vertices.iterator();
		int i;
		while (iter.hasNext()) {
			i = iter.next().intValue();
			_characteristicV[i] = true;
		}
		return _characteristicV;
	}

	public static ArrayList<boolean[]> populateOneClass(RMP rmp, ColorClass colClass) throws GRBException {
		int u, v, w, n = rmp.noVertices;
		int[] clustersV = rmp.clustersV;
		boolean[] charColClassN = new boolean[n];
		boolean[][] adjacency = rmp.adjacencyM;
		ArrayList<boolean[]> CharColClList = new ArrayList<boolean[]>();
		ArrayList<Integer> hSet, delta = new ArrayList<Integer>();
		Iterator<Integer> iter = colClass.vertices.iterator();

		iter = colClass.vertices.iterator();
		while (iter.hasNext()) {
			u = iter.next().intValue();
			charColClassN = characteristicV(colClass, n);
			charColClassN[u] = false;
			hSet = buildInitialHSet(clustersV, adjacency, charColClassN, n, u);
			while (hSet != null && hSet.size() > 0) {
				v = hSet.remove(hSet.size() - 1);
				charColClassN = characteristicV(colClass, n);
				charColClassN[u] = false;
				charColClassN[v] = true;
				delta = buildHSet(clustersV, adjacency, charColClassN, hSet, n);
				while (delta != null && delta.size() > 0) {
					w = delta.get(0);
					charColClassN[w] = true;
					hSet.remove((Integer) w);
					delta = buildHSet(clustersV, adjacency, charColClassN, hSet, n);
				}
				CharColClList.add(charColClassN);
			}
		}
		/////////////
		return CharColClList;
	}

	public static RMP addClassesPopulateNew(RMP rmp, int[] colored) throws GRBException {
		int _max = -1, n = rmp.noVertices;
		ColorClass colClass;
		ArrayList<boolean[]> CharColClList = new ArrayList<boolean[]>();
		for (int l = 0; l < n; l++)
			if (colored[l] > _max)
				_max = colored[l];

		for (int l = 0; l < _max; l++) {
			boolean[] charCol = new boolean[n];
			for (int j = 0; j < n; j++)
				if (colored[j] == l)
					charCol[j] = true;
			colClass = new ColorClass(charCol);
			colClass.toString();
			CharColClList = populateOneClass(rmp, colClass);
			if (rmp.check(colClass, n))
				rmp = addClass_Improved(rmp, colClass);

			Iterator<boolean[]> iter = CharColClList.iterator();
			while (iter.hasNext()) {
				colClass = new ColorClass(iter.next());
				if (rmp.check(colClass, n))
					rmp = addClass(rmp, colClass);
			}
		}
		return rmp;
	}

	public static RMP addClassesPopulateNew_Improved(RMP rmp, int[] colored) throws GRBException {
		int _max = -1, n = rmp.noVertices;
		ColorClass colClass;
		ArrayList<boolean[]> CharColClList = new ArrayList<boolean[]>();
		for (int l = 0; l < n; l++)
			if (colored[l] > _max)
				_max = colored[l];

		for (int l = 0; l < _max; l++) {
			boolean[] charCol = new boolean[n];
			for (int j = 0; j < n; j++)
				if (colored[j] == l)
					charCol[j] = true;
			colClass = new ColorClass(charCol);
			colClass.toString();
			CharColClList = populateOneClass(rmp, colClass);
			if (rmp.check(colClass, n))
				rmp = addClass_Improved(rmp, colClass);

			Iterator<boolean[]> iter = CharColClList.iterator();
			while (iter.hasNext()) {
				colClass = new ColorClass(iter.next());
				if (rmp.check(colClass, n))
					rmp = addClass_Improved(rmp, colClass);
			}
		}
		return rmp;
	}

	public static RMP addClassesPopulate(RMP rmp, int[] colored) throws GRBException {
		int v, w, n = rmp.noVertices, k = rmp.noClusters, p;
		Integer t = null;
		boolean addVertex = true;
		for (int h = 0; h < k; h++) {
			p = 0;
			boolean[] characteristic = new boolean[n], unCharacteristic = new boolean[n];

			for (int i = 0; i < n; i++)
				unCharacteristic[i] = true;
			for (int i = 0; i < n; i++)
				if (colored[i] == h) {
					characteristic[i] = true;
					unCharacteristic[i] = false;
					p++;
				}
			ColorClass currentClass = new ColorClass(characteristic);
			ColorClass complementClass = new ColorClass(unCharacteristic);

			if (p > 1) {
				ColorClass newClass = new ColorClass(characteristic);
				if (rmp.check(newClass, n))
					rmp = addClass_Improved(rmp, newClass);

				Iterator<Integer> vertexIterator = currentClass.vertices.iterator();
				while (vertexIterator.hasNext()) {
					ColorClass setH = new ColorClass();
					int u = vertexIterator.next().intValue();
					newClass = new ColorClass(currentClass);
					newClass.vertices.remove(u);
					Iterator<Integer> vertexIterator2;
					Iterator<Integer> vertexIterator3 = complementClass.vertices.iterator();
					while (vertexIterator3.hasNext()) {
						addVertex = true;
						v = vertexIterator3.next().intValue();
						vertexIterator2 = newClass.vertices.iterator();
						while (vertexIterator2.hasNext()) {
							w = vertexIterator2.next().intValue();
							if (rmp.adjacencyM[v][w] || rmp.clustersV[v] == rmp.clustersV[w])
								addVertex = false;
						}
						if (addVertex)
							setH.vertices.add(v);
					}
					if (setH.vertices != null) {
						setH.size = setH.vertices.size();
						while (setH.size > 0) {
							vertexIterator2 = setH.vertices.iterator();
							v = vertexIterator2.next().intValue();
							newClass = new ColorClass(currentClass);
							newClass.vertices.remove(u);
							newClass.vertices.add(v);
							setH.vertices.remove(v);
							setH.size = setH.vertices.size();
							t = getVertex(rmp, setH, newClass);
							if (t != null) {
								while (t != null) {
									w = t.intValue();
									setH.vertices.remove(w);
									setH.size = setH.vertices.size();
									newClass.vertices.add(w);
									if (setH.size > 0) {
										t = getVertex(rmp, setH, newClass);
									} else
										t = null;
								}
								if (rmp.check(newClass, n))
									rmp = addClass_Improved(rmp, newClass);
							}
						}
					}
				}
			}
		}
		return rmp;
	}

	public static Integer getVertex(RMP rmp, ColorClass setH, ColorClass newClass) {
		Integer e = null;
		boolean addVertex = true;
		int v, w;
		Iterator<Integer> vertexIterator1 = setH.vertices.iterator();
		while (vertexIterator1.hasNext()) {
			addVertex = true;
			v = vertexIterator1.next().intValue();
			Iterator<Integer> vertexIterator2 = newClass.vertices.iterator();
			while (vertexIterator2.hasNext()) {
				w = vertexIterator2.next().intValue();
				if (rmp.adjacencyM[v][w] || rmp.clustersV[v] == rmp.clustersV[w])
					addVertex = false;
			}
			if (addVertex)
				return v;
		}
		return e;
	}

	public static RMP solveRMP_Pool(String fileName, RMP rmp, int noPb, int poolSize) throws GRBException {
		double[] dualsCluster = new double[rmp.noClusters];
		int[] dualC_index = new int[rmp.noClusters];
		ColorClass[] newStableSet = null;
		long start = System.nanoTime();
		int h = 0, s = 0, l = 0, optStat;
		GRBEnv env = new GRBEnv();
		do {
			long execTime1 = System.nanoTime();
			h++;
			// System.out.println("Entering column generation step") - (RMP);
			rmp.model.set(GRB.IntParam.Method, 0); // 0 = primal
			rmp.model.set(GRB.IntParam.OutputFlag, 0);
			rmp.model.update();
			String path = "../data/PartitionCol/results/";
			rmp.model.optimize();
			optStat = rmp.model.get(GRB.IntAttr.Status);// solve the RMP
			rmp.mStatus = optStat;
			System.out.println("Optimum RMP: " + rmp.model.get(DoubleAttr.ObjVal));
			// get the dual variables in order to build the subproblem:
			for (int j = 0; j < rmp.noClusters; j++)
				dualC_index[j] = -1;
			l = 0;
			for (int j = 0; j < rmp.noClusters; j++)
				if (rmp.model.getConstrByName("cluster_" + j) != null) {
					dualsCluster[l] = rmp.model.getConstrByName("cluster_" + j).get(GRB.DoubleAttr.Pi);
					// TODO: in B&B one must use these indexes:
					dualC_index[l] = j;
					l++;
				}
			SubProblem _subProblem = new SubProblem(env, fileName, rmp, noPb, rmp.adjacencyM, rmp.clustersV,
					dualsCluster, dualC_index, poolSize, rmp.noVertices, rmp.noVertices, h);
			s = rmp.noVertices;
			newStableSet = _subProblem.solvePool(fileName, s, precisionRC, rmp.adjacencyM, h, poolSize);
			System.out.println();
			if (newStableSet != null)
				for (int q = 0; q < newStableSet.length; q++) {
					if (rmp.check(newStableSet[q], rmp.noVertices))
						addClass(rmp, newStableSet[q]);
					else
						newStableSet[q].toString();
				}
			execTime1 = System.nanoTime() - execTime1;
		} while (newStableSet != null && optStat != GRB.Status.INFEASIBLE && optStat != GRB.Status.UNBOUNDED);
		System.out.println("Column generation total execution time = " + (System.nanoTime() - start) * 1e-9);
		if (optStat != GRB.Status.INFEASIBLE || optStat != GRB.Status.UNBOUNDED)
			System.out.println("Subproblem infeasible or unbounded");
		System.out.println(" *** END ***");
		System.out.println();
		return rmp;
	}

	public static RMP solveRMP_Pool_Improved(String fileName, RMP rmp, int noPb, int poolSize) throws GRBException {
		double[] dualsCluster = new double[rmp.noClusters];
		ColorClass[] newStableSet = null;
		long start = System.nanoTime();
		int h = 0, s = 0, l = 0, optStat;
		GRBEnv env = new GRBEnv();
		do {
			long execTime1 = System.nanoTime();
			h++;
			rmp.model.set(GRB.IntParam.Method, 0); // 0 = primal
			rmp.model.set(GRB.IntParam.OutputFlag, 0);
			rmp.model.update();
			rmp.model.optimize();
			optStat = rmp.model.get(GRB.IntAttr.Status);// solve the RMP
			rmp.mStatus = optStat;
			// get the dual variables in order to build the subproblem:
			for (int j = 0; j < rmp.noClusters; j++)
				if (rmp.model.getConstrByName("cluster_" + j) != null)
					dualsCluster[j] = rmp.model.getConstrByName("cluster_" + j).get(GRB.DoubleAttr.Pi);
			SubProblem _subProblem = new SubProblem(env, fileName, rmp, noPb, rmp.adjacencyM, rmp.clustersV,
					dualsCluster, poolSize, rmp.noVertices, rmp.noClusters, h);
			s = rmp.noVertices;
			newStableSet = _subProblem.solvePool(fileName, s, precisionRC, rmp.adjacencyM, h, poolSize);
			if (newStableSet != null)
				for (int q = 0; q < newStableSet.length; q++) {
					if (rmp.check(newStableSet[q], rmp.noVertices))
						addClass_Improved(rmp, newStableSet[q]);
				}
			execTime1 = System.nanoTime() - execTime1;
		} while (newStableSet != null && optStat != GRB.Status.INFEASIBLE && optStat != GRB.Status.UNBOUNDED);
		System.out.println("Column generation total execution time = " + (System.nanoTime() - start) * 1e-9);
		if (optStat != GRB.Status.INFEASIBLE || optStat != GRB.Status.UNBOUNDED)
			System.out.println(" *** END ***");
		System.out.println();
		// printSolution(rmp.model);
		rmp.noSubProblems = h;
		return rmp;
	}

	public static RMP solveRMP_PoolImproved(String fileName, RMP rmp, int noPb, int poolSize) throws GRBException {
		double[] dualsCluster = new double[rmp.noClusters];
		int[] dualC_index = new int[rmp.noClusters];
		ColorClass[] newStableSet = null;
		long start = System.nanoTime();
		int h = 0, s = 0, l = 0, optStat;
		GRBEnv env = new GRBEnv();
		do {
			long execTime1 = System.nanoTime();
			h++;
			rmp.model.set(GRB.IntParam.Method, 0); // 0 = primal
			rmp.model.set(GRB.IntParam.OutputFlag, 0);
			rmp.model.update();
			String path = "../data/PartitionCol/results/";
			rmp.model.write(path + fileName + "/pb" + noPb + "_ImprovedMainModel_before_h_" + h + ".lp");
			rmp.model.optimize();
			optStat = rmp.model.get(GRB.IntAttr.Status);// solve the RMP
			rmp.mStatus = optStat;
			rmp.model.write(path + fileName + "/pb" + noPb + "_MainModel_before_h_" + h + ".sol");
			System.out.println("Optimum RMP: " + rmp.model.get(DoubleAttr.ObjVal));
			// get the dual variables in order to build the subproblem:
			for (int j = 0; j < rmp.noClusters; j++)
				dualC_index[j] = -1;
			l = 0;
			for (int j = 0; j < rmp.noClusters; j++)
				if (rmp.model.getConstrByName("cluster_" + j) != null) {
					dualsCluster[l] = rmp.model.getConstrByName("cluster_" + j).get(GRB.DoubleAttr.Pi);
					dualC_index[l] = j;
					l++;
				}
			SubProblem _subProblem = new SubProblem(env, fileName, rmp, noPb, rmp.adjacencyM, rmp.clustersV,
					dualsCluster, dualC_index, poolSize, rmp.noVertices, rmp.noVertices, h);
			s = rmp.noVertices;
			newStableSet = _subProblem.solvePool(fileName, s, precisionRC, rmp.adjacencyM, h, poolSize);
			System.out.println();
			if (newStableSet != null)
				for (int q = 0; q < newStableSet.length; q++) {
					if (rmp.check(newStableSet[q], rmp.noVertices))
						addClass(rmp, newStableSet[q]);
					else
						newStableSet[q].toString();
				}
			execTime1 = System.nanoTime() - execTime1;
		} while (newStableSet != null && optStat != GRB.Status.INFEASIBLE && optStat != GRB.Status.UNBOUNDED);
		System.out.println("Column generation total execution time = " + (System.nanoTime() - start) * 1e-9);
		if (optStat != GRB.Status.INFEASIBLE || optStat != GRB.Status.UNBOUNDED)
			System.out.println(" *** END ***");
		System.out.println();
		return rmp;
	}

	public static RMP addClass(RMP rmp, ColorClass newStableSet) throws GRBException {
		String path = "../data/PartitionCol/results/";
		int p = newStableSet.vertices.size(), h = 0, iCluster, iNode;
		rmp.model.set(GRB.IntParam.OutputFlag, 0);
		Iterator<Integer> iter = newStableSet.vertices.iterator();
		if (newStableSet.vertices.size() > 0) {
			p = 0;
			iter = newStableSet.vertices.iterator();
			while (iter.hasNext())
				if (rmp.model.getConstrByName("cluster_" + rmp.clustersV[iter.next().intValue()]) != null)
					p++;
			double[] coeffConstr = new double[p];
			GRBConstr[] newConstr = new GRBConstr[p];
			iter = newStableSet.vertices.iterator();
			h = 0;
			System.out.println("Adding var x" + noOfCreatedClasses);
			newStableSet.toString();
			System.out.println();
			while (iter.hasNext()) {
				iNode = iter.next().intValue();
				iCluster = rmp.clustersV[iNode];
				rmp.vertexColCl[iNode].add((Integer) noOfCreatedClasses);
				newConstr[h] = rmp.model.getConstrByName("cluster_" + iCluster);
				rmp.clusterColCl[iCluster].add(noOfCreatedClasses);
				coeffConstr[h] = 1.0;
				rmp.model.update();
				h++;
			}
			try {
				rmp.model.addVar(0, GRB.INFINITY, newStableSet.vertices.size() - 1, GRB.CONTINUOUS, newConstr,
						coeffConstr, "x" + noOfCreatedClasses);
			} catch (GRBException e) {
				System.out.println("Error: " + e.getErrorCode());
				System.out.println("var " + noOfCreatedClasses);
				newStableSet.toString();
			}
			rmp.model.update();
			rmp.colClList.put(noOfCreatedClasses, newStableSet);
			noOfCreatedClasses++;
		}
		return rmp;
	}

	public static RMP addClass_Improved(RMP rmp, ColorClass newStableSet) throws GRBException {
		int p = newStableSet.vertices.size(), h = 0, iCluster, iNode;
		double[] coeffConstr = new double[p];
		GRBConstr[] newConstr = new GRBConstr[p];
		rmp.model.set(GRB.IntParam.OutputFlag, 0);
		Iterator<Integer> iter = newStableSet.vertices.iterator();
		// System.out.println("Adding var x" + noOfCreatedClasses);
		// newStableSet.toString();
		// System.out.println();
		while (iter.hasNext()) {
			iNode = iter.next().intValue();
			iCluster = rmp.clustersV[iNode];
			rmp.vertexColCl[iNode].add((Integer) noOfCreatedClasses);
			newConstr[h] = rmp.model.getConstrByName("cluster_" + iCluster);
			rmp.clusterColCl[iCluster].add(noOfCreatedClasses);
			coeffConstr[h] = 1.0;
			h++;
		}
		try {
			rmp.model.addVar(0, GRB.INFINITY, newStableSet.vertices.size() - 1, GRB.CONTINUOUS, newConstr, coeffConstr,
					"x" + noOfCreatedClasses);
		} catch (GRBException e) {
			System.out.println("Error: " + e.getErrorCode());
			System.out.println("dd------------");
			System.out.println("var " + noOfCreatedClasses);
			System.out.println("dd------------");
		}
		rmp.model.update();
		rmp.colClList.put(noOfCreatedClasses, newStableSet);
		if (p > rmp.maxClassCard)
			rmp.maxClassCard = p;
		noOfCreatedClasses++;
		return rmp;
	}

	public static boolean verifyStability(ColorClass _class, int j) {
		int i;
		Iterator<Integer> iter1;
		if (_class.vertices == null)
			return true;
		else {
			iter1 = _class.vertices.iterator();
			while (iter1.hasNext()) {
				i = iter1.next().intValue();
				if (adjacency[i][j])
					return false;
			}
		}
		return true;
	}

	public static Pair branching(int _noClusters, int[] _clustersV, int[] _vertex, GRBModel _model,
			HashMap<Integer, ColorClass> _colClList) throws GRBException {
		boolean isInteger = true;
		Pair pair = new Pair();
		int _i = -1, _j = -1, iC = -1, jC = -1, s1, s2, k = _noClusters, h, hh;
		double max = precisionOpt, val;
		double[][] _sums = new double[k][k], _maxes = new double[k][k];
		int[][] _index1 = new int[k][k], _index2 = new int[k][k];
		Integer tt;
		ColorClass _colClass;
		Iterator<Integer> iter1, iter2;
		GRBVar[] vars = _model.getVars();
		GRBVar var;
		String varName;
		for (int p = 0; p < vars.length; p++) {
			var = vars[p];
			varName = var.get(GRB.StringAttr.VarName);
			h = varName.indexOf('x');
			if (h != -1) {
				hh = Integer.valueOf(varName.substring(h + 1));
				val = var.get(GRB.DoubleAttr.X);
				if (Math.abs(val) > 1e-7 && Math.abs(1 - val) > 1e-7) {
					System.out.println("Non integral solution, x" + hh + " = " + val);
					isInteger = false;
					break;
				}
			}
		}
		////////////
		if (!isInteger) {
			for (HashMap.Entry<Integer, ColorClass> entry : _colClList.entrySet()) {
				tt = entry.getKey();
				_colClass = entry.getValue();
				val = _model.getVarByName("x" + tt.intValue()).get(GRB.DoubleAttr.X);
				iter1 = _colClass.vertices.iterator();
				while (iter1.hasNext()) {
					s1 = iter1.next().intValue();
					iter2 = _colClass.vertices.iterator();
					while (iter2.hasNext()) {
						s2 = iter2.next().intValue();
						if (s1 != s2) {
							_sums[_clustersV[s1]][_clustersV[s2]] += val;
							if (val > _maxes[_clustersV[s1]][_clustersV[s2]]) {
								_maxes[_clustersV[s1]][_clustersV[s2]] = val;
								_index1[_clustersV[s1]][_clustersV[s2]] = s1;
								_index2[_clustersV[s1]][_clustersV[s2]] = s2;
							}
						}
					}
				}
			}
			for (int i = 0; i < k; i++)
				for (int j = 0; j < i; j++)
					if (_sums[i][j] > 0 && _sums[i][j] < 1 - precisionBB && _sums[i][j] > max) {
						max = _sums[i][j];
						_i = _index1[i][j];
						_j = _index2[i][j];
						iC = i;
						jC = j;
					}
			if (_i != -1 && _j != -1)
				pair = new Pair(_vertex[_i], _vertex[_j], _i, _j, -1);

		}
		if (iC != -1 && jC != -1)
			System.out.println("Branching on i, j: " + _i + ", " + _j);
		return pair;
	}

	public static void cutAndBranchAndPrice(String fileName, int n_max, double gap, double bdStop, int poolSize)
			throws GRBException, IOException {

		double bestIntOpt = 1e10, crtOpt = 0.0, noOfcolors, root_time1 = 0, noOfVariables = 0, rootNoOfVariables = 0,
				aux, _noRestoredClasses = 0, _totalNoRestoredClasses = 0, _noSubProblems = 0, _rootNoSubProblems = 0;
		int pbNo = 0, _modelFSt = -1, noFacets = rootNoOfFacetsPerCluster, noMClqFacets = rootNoOfMajClqFacetsPerSize;
		boolean found = false;
		long exTime1 = System.nanoTime(), exTime2 = System.nanoTime();
		String path = "../data/PartitionCol/results/" + fileName;
		Pair branchPair;
		GRBModel _modelfacets;

		stackRMPb = new Stack<RMP>();
		createDir(path);
		readFile(fileName);
		RMP rmp = buildInitialLPModelSlack(fileName, deterministicInitialStage);
		System.out.println("*******Build time for the initial problem: " + (System.nanoTime() - exTime1) * 1e-9);
		stackRMPb.add(rmp);
		while (!stackRMPb.isEmpty() && pbNo < n_max && !found) {
			rmp = stackRMPb.pop();
			pbNo++;
			_noRestoredClasses = rmp.noRestoredClasses;
			_totalNoRestoredClasses += _noRestoredClasses;
			System.out.println();
			System.out.println("******* Problem " + pbNo + " ******* ");
			System.out.println("No of vertices: " + rmp.noVertices + " | No. of clusters: " + rmp.noClusters
					+ " | No of restored variables: " + _noRestoredClasses);
			if (rmp.sameColNodes != null && rmp.sameColNodes.size() > 0)
				System.out.println(
						rmp.type + " | pair: from = " + rmp.sameColNodes.get(rmp.sameColNodes.size() - 1).fromId
								+ ", to " + rmp.sameColNodes.get(rmp.sameColNodes.size() - 1).toId);
			exTime1 = System.nanoTime();
			rmp = solveRMP_Pool_Improved(fileName, rmp, pbNo, poolSize);
			crtOpt = rmp.model.get(DoubleAttr.ObjVal);
			noOfcolors = rmp.noClusters - crtOpt;
			noOfVariables += rmp.colClList.size();
			_noSubProblems += rmp.noSubProblems;
			System.out.println("Optimum: " + crtOpt + ", number of ''colors'': " + noOfcolors);
			// Adding facets defining inequalities:
			if (pbNo > 1) {
				noFacets = nodeNoOfFacetsPerCluster;
				noMClqFacets = nodeNoOfMajClqFacetsPerSize;
			}
			_modelfacets = facetsIneqModel(rmp, crtOpt, noFacets, noMClqFacets, fileName, pbNo);
			aux = crtOpt;
			if (nodeNoOfFacetsPerCluster > 0 || nodeNoOfMajClqFacetsPerSize > 0) {
				aux = _modelfacets.get(DoubleAttr.ObjVal);
				crtOpt = aux;
			}
			if (pbNo == 1 && (rootNoOfFacetsPerCluster > 0 || rootNoOfMajClqFacetsPerSize > 0)) {
				aux = _modelfacets.get(DoubleAttr.ObjVal);
				crtOpt = aux;
			}
			noOfcolors = rmp.noClusters - crtOpt;
			// change the significance of variable aux:
			aux = lowerBound(rmp.noClusters - aux);
			exTime1 = System.nanoTime() - exTime1;
			if (pbNo == 1) {
				rootNoOfVariables = rmp.colClList.size();
				_rootNoSubProblems = rmp.noSubProblems;
				rootLowerB = lowerBound(noOfcolors);
				if (rootLowerB > aux) {
					rootLowerB = aux;
					System.out.println("On facets");
				}
				root_time1 = exTime1 * 1e-9;
			}
			System.out.println("******* Execution time for problem " + pbNo + ": " + exTime1 * 1e-9);
			_modelFSt = _modelfacets.get(GRB.IntAttr.Status);
			if (_modelFSt != GRB.Status.INFEASIBLE && _modelFSt != GRB.Status.UNBOUNDED
					&& _modelFSt != GRB.Status.INF_OR_UNBD && noOfcolors < bestIntOpt - precisionBB) {
				branchPair = branching(rmp.noClusters, rmp.clustersV, rmp.vertex, _modelfacets, rmp.colClList);
				if (branchPair.from != -1) {
					stackRMPb.add(buildLPModelPairAddEdge(rmp, branchPair, fileName));
					stackRMPb.add(buildLPModelPairContraction(rmp, branchPair, fileName, pbNo));
				} else {
					System.out.println("Integral solution for problem no." + pbNo);
					ShowCPCProblem(rmp.noVertices, rmp.noClusters, rmp.clustersV, _modelfacets, rmp.colClList, pbNo);
					if (noOfcolors < bestIntOpt)
						bestIntOpt = noOfcolors;
					if (Math.abs(bestIntOpt - rootLowerB) < precisionOpt)
						break;
				}
			}
		}
		exTime2 = System.nanoTime() - exTime2;
		System.out.println();
		System.out.println("****************************END*******************************");

		System.out.println("Found number of colors: " + bestIntOpt + ". Root lower bound: " + rootLowerB);
		System.out.println("Total time: " + exTime2 * 1e-9 + " | time per node: " + exTime2 * 1e-9 / pbNo
				+ " | time per node (without root): " + (exTime2 - root_time1) * 1e-9 / (pbNo - 1) + " | root time: "
				+ root_time1);
		System.out.println("Root no of variables: " + rootNoOfVariables);
		System.out.println("Number of newly generated variables: " + (noOfVariables - _totalNoRestoredClasses)
				+ " | no of newly generated variables per problem: "
				+ (noOfVariables - _totalNoRestoredClasses) / (pbNo - 1));
		System.out.println(
				"Total no of subproblems: " + _noSubProblems + " | root no of subproblems: " + _rootNoSubProblems);
		System.out.println("No of subproblems per node: " + (_noSubProblems / pbNo)
				+ " | root no of subproblems per node (without root): "
				+ (_noSubProblems - _rootNoSubProblems) / (pbNo - 1));
		System.out.println("***********************************************************");
	}

	public static void branchAndPrice(String fileName, int n_max, double gap, double bdStop, int poolSize)
			throws GRBException, IOException {
		int pbNo = 0, _modelSt = -1;
		double bestIntOpt = 1e10, crtOpt = 0.0, noOfcolors, root_time1 = 0, root_time2 = 0, rootNoOfcolors = -1,
				noOfVariables = 0, rootNoOfVariables = 0, aux, _noRestoredClasses = 0, _totalNoRestoredClasses = 0,
				_noSubProblems = 0, _rootNoSubProblems = 0;
		boolean found = false;
		long exTime1 = System.nanoTime(), exTime2 = System.nanoTime(), exTime3 = 0, exTime2i = 0;
		String path = "../data/PartitionCol/results/" + fileName;
		Pair branchPair;

		stackRMPb = new Stack<RMP>();
		createDir(path);
		readFile(fileName);
		RMP rmp = buildInitialLPModelSlack(fileName, deterministicInitialStage);
		System.out.println("*******Build time for the initial problem: ");
		stackRMPb.add(rmp);
		while (!stackRMPb.isEmpty() && pbNo < n_max && !found) {
			rmp = stackRMPb.pop();
			pbNo++;
			_noRestoredClasses = rmp.noRestoredClasses;
			_totalNoRestoredClasses += _noRestoredClasses;
			System.out.println();
			System.out.println("******* Problem " + pbNo + " ******* ");
			System.out.println("No of vertices: " + rmp.noVertices + " | No. of clusters: " + rmp.noClusters
					+ " | No of restored variables: " + _noRestoredClasses);
			if (rmp.sameColNodes != null && rmp.sameColNodes.size() > 0)
				System.out.println(
						rmp.type + " | pair: from = " + rmp.sameColNodes.get(rmp.sameColNodes.size() - 1).fromId
								+ ", to " + rmp.sameColNodes.get(rmp.sameColNodes.size() - 1).toId);
			exTime1 = System.nanoTime();
			rmp = solveRMP_Pool_Improved(fileName, rmp, pbNo, poolSize);
			crtOpt = rmp.model.get(DoubleAttr.ObjVal);
			noOfcolors = rmp.noClusters - crtOpt;
			noOfVariables += rmp.colClList.size();
			_noSubProblems += rmp.noSubProblems;
			System.out.println(" | No. of variables: " + rmp.colClList.size() + " for problem no " + pbNo
					+ " | Optimum: " + crtOpt + ", number of ''colors'': " + noOfcolors + ", no of solved subproblems: "
					+ rmp.noSubProblems);
			// Adding facets defining inequalities:
			if (pbNo == 1) {
				rootNoOfVariables = rmp.colClList.size();
				rootLowerB = lowerBound(noOfcolors);
				_rootNoSubProblems = rmp.noSubProblems;
				root_time1 = (System.nanoTime() - exTime1) * 1e-9;
			}
			System.out.println(
					"******* Execution time for problem " + pbNo + ": " + (System.nanoTime() - exTime1) * 1e-9);
			_modelSt = rmp.model.get(GRB.IntAttr.Status);
			if (_modelSt != GRB.Status.INFEASIBLE && _modelSt != GRB.Status.UNBOUNDED
					&& _modelSt != GRB.Status.INF_OR_UNBD && noOfcolors < bestIntOpt - precisionBB) {
				branchPair = branching(rmp.noClusters, rmp.clustersV, rmp.vertex, rmp.model, rmp.colClList);
				if (branchPair.from != -1) {
					stackRMPb.add(buildLPModelPairAddEdge(rmp, branchPair, fileName));
					stackRMPb.add(buildLPModelPairContraction(rmp, branchPair, fileName, pbNo));
				} else {
					System.out.println("Integral solution for problem no." + pbNo);
					ShowCPCProblem(rmp.noVertices, rmp.noClusters, rmp.clustersV, rmp.model, rmp.colClList, pbNo);
					System.out.println("No of vertices: " + rmp.noVertices + ", no of clusters: " + rmp.noClusters
							+ ", no of colors for current problem: " + noOfcolors);
					if (noOfcolors < bestIntOpt)
						bestIntOpt = noOfcolors;
					exTime2i = (System.nanoTime() - exTime2);
					System.out.println();
					System.out.println("***************************Integral Solution****************************");
					System.out.println();
					System.out.println("First integral solution, time: " + exTime2i * 1e-9);
					System.out.println("Found number of colors: " + bestIntOpt + ". Root lower bound: " + rootLowerB);
					System.out.println("Total time: " + exTime2i * 1e-9 + " | time per node: " + exTime2i * 1e-9 / pbNo
							+ " | time per node (without root): " + (exTime2i - root_time2) * 1e-9 / (pbNo - 1));
					System.out.println(
							"Root time: " + root_time1 + " | root time (including branching): " + root_time2 * 1e-9);
					System.out.println("Root no of variables: " + rootNoOfVariables);
					System.out
							.println("Number of newly generated variables: " + (noOfVariables - _totalNoRestoredClasses)
									+ " | no of newly generated variables per problem: "
									+ (noOfVariables - _totalNoRestoredClasses) / (pbNo - 1));
					System.out.println("Total no of subproblems: " + _noSubProblems + " | root no of subproblems: "
							+ _rootNoSubProblems);
					System.out.println("No of subproblems per node: " + (_noSubProblems / pbNo)
							+ " | root no of subproblems per node (without root): "
							+ (_noSubProblems - _rootNoSubProblems) / (pbNo - 1));
					System.out.println("***********************************************************");
					if (Math.abs(bestIntOpt - rootLowerB) < precisionOpt)
						break;
				}
			}
			exTime1 = System.nanoTime() - exTime1;
			if (pbNo == 1)
				root_time2 = exTime1;
			System.out.println(
					"**************Total (including branching) time for problem " + pbNo + ": " + exTime1 * 1e-9);
		}
		exTime2 = System.nanoTime() - exTime2;
		System.out.println();
		System.out.println("***************************END****************************");
		System.out.println();

		System.out.println("Found number of colors: " + bestIntOpt + ". Root lower bound: " + rootLowerB);
		System.out.println("Total time: " + exTime2 * 1e-9 + " | time per node: " + exTime2 * 1e-9 / pbNo
				+ " | time per node (without root): " + (exTime2 - root_time2) * 1e-9 / (pbNo - 1));
		System.out.println("root time: " + root_time1 + " | root time (including branching): " + root_time2 * 1e-9);
		System.out.println("Root no of variables: " + rootNoOfVariables);
		System.out.println("Number of newly generated variables: " + (noOfVariables - _totalNoRestoredClasses)
				+ " | no of newly generated variables per problem: "
				+ (noOfVariables - _totalNoRestoredClasses) / (pbNo - 1));
		System.out.println(
				"Total no of subproblems: " + _noSubProblems + " | root no of subproblems: " + _rootNoSubProblems);
		System.out.println("No of subproblems per node: " + (_noSubProblems / pbNo)
				+ " | No of subproblems per node (without root): "
				+ (_noSubProblems - _rootNoSubProblems) / (pbNo - 1));
		System.out.println("***********************************************************");
	}

	public static void main(String[] args) throws GRBException, IOException, InterruptedException {
		// test();
		String fileName = "ring_n15p0.5s1.pcp";//"n90p2t2s1.pcp";// "ring_n20p1.0s1.pcp";
		String path = "../data/PartitionCol/results/";
		int n_max = 300, poolSize = 15;
		double gap = 1e-8, bdStop = 1;

		deterministicInitialStage = true;
		upperB = 1e20;
		rootLowerB = -1e20;
		noStages = 1;
		rootNoOfFacetsPerCluster = 0;
		nodeNoOfFacetsPerCluster = 0;
		rootNoOfMajClqFacetsPerSize = 0;
		nodeNoOfMajClqFacetsPerSize = 0;

		createDir(path + fileName);
		readFile(fileName);

		branchAndPrice(fileName, n_max, gap, bdStop, poolSize);
		//cutAndBranchAndPrice(fileName, n_max, gap, bdStop, poolSize);
	}
}