import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map.Entry;

import gurobi.GRB;
import gurobi.GRBEnv;
import gurobi.GRBException;
import gurobi.GRBModel;
import gurobi.GRBVar;

public class RMP {
	// the model corresponding to this problem:
	public GRBModel model;
	// the number of solved subproblems:
	public int noSubProblems;
	// the number of restored classes:
	public int noRestoredClasses;
	// the number of the first class:
	public int firstClassNo;
	// the number of vertices:
	public int noVertices;
	// the real id's of vertices:
	public int[] vertex;
	// the number of clusters:
	public int noClusters;
	// the real id's of clusters:
	// TODO: to remove?
	public int[] cluster;
	// the clusters:
	public int[] clustersV;
	// the adjacency matrix:
	public boolean[][] adjacencyM;
	// vertexColCl[i] keeps the id(s) for the active stable sets containing
	// vertex i:
	public ArrayList<Integer>[] vertexColCl;
	// clusterColCl[j] keeps the id(s) for the active stable sets
	// intersecting cluster j:
	public ArrayList<Integer>[] clusterColCl;
	// clusterColClClq[j] keeps the id(s) for the active stable sets in a
	// clique (from the intersection graph) extending the clique of the stable sets
	// intersecting cluster j:
	public ArrayList<Integer>[] clusterColClClq;
	public ArrayList<Pair> sameColNodes;
	public ArrayList<Pair> diffColNodes;
	// the index of variables for the active coloring classes:
	public HashMap<Integer, ColorClass> colClList = new HashMap<Integer, ColorClass>();
	// the model status:
	public int mStatus;
	// type of the problem (root, contraction, edge-adding)
	public String type;
	// the maximum cardinality of a color class;
	public int maxClassCard;
	// color classes by cardinality:
	public LinkedList<ArrayList<Integer>> classesByCard = new LinkedList<ArrayList<Integer>>();

	public RMP(GRBEnv env, int n, int k) throws GRBException {
		this.model = new GRBModel(env);
		this.vertexColCl = new ArrayList[n];
		this.clusterColCl = new ArrayList[k];
	}

	public RMP(GRBModel _model, int _firstClassNo, int _noRestoredClasses, int _noVert, int[] _vertex, int _noClust,
			int[] _cluster, boolean[][] _adjacencyM, int[] _clustersV, ArrayList<Integer>[] _vertexCC,
			ArrayList<Integer>[] _clusterCC, ArrayList<Integer>[] _clusterCCC, String _nume, ArrayList<Pair> _diffCV,
			ArrayList<Pair> _sameCV, HashMap<Integer, ColorClass> _colorClassesList, String _type, int _maxClassCard)
			throws GRBException {
		this.model = new GRBModel(_model);
		this.firstClassNo = _firstClassNo;
		this.noRestoredClasses = _noRestoredClasses;
		this.type = _type;
		this.maxClassCard = _maxClassCard;

		this.noVertices = _noVert;
		int[] vertex = new int[_noVert];
		for (int i = 0; i < _noVert; i++)
			vertex[i] = _vertex[i];
		this.vertex = vertex;

		this.noClusters = _noClust;
		int[] cluster = new int[_noClust];
		for (int i = 0; i < _noClust; i++)
			cluster[i] = _cluster[i];
		this.cluster = cluster;

		boolean[][] adjM = new boolean[_noVert][_noVert];
		for (int i = 0; i < _noVert; i++)
			for (int j = 0; j < _noVert; j++)
				adjM[i][j] = _adjacencyM[i][j];
		this.adjacencyM = adjM;

		int[] clustersV = new int[_noVert];
		for (int i = 0; i < _noVert; i++)
			clustersV[i] = _clustersV[i];
		this.clustersV = clustersV;

		ArrayList<Integer> listV;
		ArrayList<Integer>[] vertexCoal = new ArrayList[_vertexCC.length];
		for (int i = 0; i < _vertexCC.length; i++) {
			listV = new ArrayList<Integer>();
			if (_vertexCC[i] != null) {
				Iterator<Integer> iterV = _vertexCC[i].iterator();
				while (iterV.hasNext())
					listV.add(iterV.next().intValue());
			}
			vertexCoal[i] = listV;
		}
		this.vertexColCl = vertexCoal;

		ArrayList<Integer> listC;
		ArrayList<Integer>[] clusterCoal = new ArrayList[_clusterCC.length];
		for (int i = 0; i < _clusterCC.length; i++) {
			listC = new ArrayList<Integer>();
			if (_clusterCC[i] != null) {
				Iterator<Integer> iterC = _clusterCC[i].iterator();
				while (iterC.hasNext())
					listC.add(iterC.next().intValue());
			}
			clusterCoal[i] = listC;
		}
		this.clusterColCl = clusterCoal;

		if (_clusterCCC != null) {
			ArrayList<Integer> listCClique;
			ArrayList<Integer>[] clusterClique = new ArrayList[_clusterCCC.length];
			for (int i = 0; i < _clusterCCC.length; i++) {
				listCClique = new ArrayList<Integer>();
				if (_clusterCCC[i] != null) {
					Iterator<Integer> iterCL = _clusterCCC[i].iterator();
					while (iterCL.hasNext())
						listCClique.add(iterCL.next().intValue());
				}
				clusterClique[i] = listCClique;
			}
			this.clusterColClClq = clusterClique;
		}

		ArrayList<Pair> listDiff = new ArrayList<Pair>();
		if (_diffCV != null) {
			Iterator<Pair> iterD = _diffCV.iterator();
			while (iterD.hasNext())
				listDiff.add(iterD.next());
		}
		this.diffColNodes = listDiff;

		ArrayList<Pair> listSame = new ArrayList<Pair>();
		if (_sameCV != null) {
			Iterator<Pair> iterS = _sameCV.iterator();
			while (iterS.hasNext())
				listSame.add(iterS.next());
		}
		this.sameColNodes = listSame;

		if (_colorClassesList != null) {
			HashMap<Integer, ColorClass> coalitionList = new HashMap<Integer, ColorClass>();
			Iterator<Entry<Integer, ColorClass>> iterVarCoal = _colorClassesList.entrySet().iterator();
			while (iterVarCoal.hasNext()) {
				HashMap.Entry<Integer, ColorClass> pairE = (HashMap.Entry<Integer, ColorClass>) iterVarCoal.next();
				coalitionList.put((Integer) pairE.getKey(), (ColorClass) pairE.getValue());
			}
			this.colClList = coalitionList;
		}
	}

	public boolean check(ColorClass stableSet, int n) {
		Iterator<Entry<Integer, ColorClass>> _class = this.colClList.entrySet().iterator();
		ColorClass currentClass;

		while (_class.hasNext()) {
			HashMap.Entry<Integer, ColorClass> pair = (HashMap.Entry<Integer, ColorClass>) _class.next();
			currentClass = (ColorClass) pair.getValue();
			if (currentClass.check(stableSet, n)) {
				return false;
			}
		}
		return true;
	}

	public ColorClass remove(int no_, ColorClass colClass, int[] _vertex, boolean[] cluster_u_Or_v) {
		ColorClass modClass = new ColorClass();
		HashSet<Integer> toRemove = new HashSet<Integer>();
		int i;
		if (colClass != null) {
			Iterator<Integer> iter = colClass.vertices.iterator();
			while (iter.hasNext()) {
				i = iter.next().intValue();
				if (cluster_u_Or_v[i])
					toRemove.add(i);
			}
			iter = toRemove.iterator();

		}
		return modClass;

	}

	public ColorClass modify(int newN, int uId, int vId, int no_, ColorClass colClass, int[] _vertex,
			boolean[] cluster_u_Or_v, boolean[][] adjacencyM) {
		int i;
		ColorClass modClass = new ColorClass();
		HashSet<Integer> toRemove = new HashSet<Integer>();

		Iterator<Integer> iter = colClass.vertices.iterator();
		while (iter.hasNext()) {
			i = iter.next().intValue();
		}

		if (colClass.vertices.contains((Integer) uId) && colClass.vertices.contains((Integer) vId)) {
			colClass.vertices.remove((Integer) uId);
			colClass.vertices.remove((Integer) vId);
			colClass.vertices.add((Integer) newN);
		} else if (colClass.vertices.contains((Integer) uId)) {
			iter = colClass.vertices.iterator();
			while (iter.hasNext()) {
				i = iter.next().intValue();
				if (cluster_u_Or_v[i])
					toRemove.add(i);
			}
			iter = toRemove.iterator();
		}

		if (colClass != null) {
			iter = colClass.vertices.iterator();
			while (iter.hasNext()) {
				i = iter.next().intValue();
				if (cluster_u_Or_v[i])
					toRemove.add(i);
			}
			iter = toRemove.iterator();

		}
		return modClass;

	}
}