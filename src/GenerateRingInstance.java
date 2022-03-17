import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.Random;

public class GenerateRingInstance {

	public GenerateRingInstance() {
	}

	public static void generateRingInst(int n, double probability, String fileName) throws IOException {
		int k = 0, i1, i2, j1, j2, k1, k2, m = 0, sens1, sens2;
		ArrayList<Pair> listP = new ArrayList<Pair>();
		Pair newP1, newP2 = new Pair();
		Random rand = new Random();
		boolean[][] M = new boolean[n][n];
		for (int i = 0; i < n; i++)
			for (int j = 0; j < i; j++) {
				if (rand.nextDouble() < probability) {
					M[i][j] = true;
					newP1 = new Pair(i, j, -1, -1, k);
					listP.add(newP1);
					k++;
					newP1 = new Pair(i, j, 1, 1, k);
					listP.add(newP1);
					k++;
				}
				if (rand.nextDouble() < probability) {
					M[j][i] = true;
					newP1 = new Pair(j, i, -1, -1, k);
					listP.add(newP1);
					k++;
					newP1 = new Pair(j, i, 1, 1, k);
					listP.add(newP1);
					k++;
				}
			}

		boolean[][] adj = new boolean[k][k];
		Iterator<Pair> iter1 = listP.iterator();
		while (iter1.hasNext()) {
			newP1 = iter1.next();
			i1 = newP1.from;
			j1 = newP1.to;
			sens1 = newP1.fromId;
			k1 = newP1.node;
			Iterator<Pair> iter2 = listP.iterator();
			while (iter2.hasNext()) {
				newP2 = iter2.next();
				i2 = newP2.from;
				j2 = newP2.to;
				sens2 = newP2.fromId;
				k2 = newP2.node;
				if (k1 != k2) {
					if (sens1 == 1 && sens2 == 1) {
						if (i1 < j1 && i2 < j2)
							if ((i2 < j1 && i1 <= i2) || ((j2 > i1) && (i2 < i1))) {
								adj[k1][k2] = true;
								adj[k2][k1] = true;
							}
						if (i1 < j1 && i2 > j2)
							if (j1 > i2 || i1 < j2) {
								adj[k1][k2] = true;
								adj[k2][k1] = true;
							}
						if (i1 > j1 && i2 < j2)
							if (j2 > i1 || i2 < j1) {
								adj[k1][k2] = true;
								adj[k2][k1] = true;
							}
						if (i1 > j1 && i2 > j2) {
							adj[k1][k2] = true;
							adj[k2][k1] = true;
						}
					}
					if (sens1 == -1 && sens2 == -1) {
						if (i1 < j1 && i2 < j2) {
							adj[k1][k2] = true;
							adj[k2][k1] = true;
						}
						if (i1 < j1 && i2 > j2)
							if (j1 < i2 || i1 > j2) {
								adj[k1][k2] = true;
								adj[k2][k1] = true;
							}
						if (i1 > j1 && i2 < j2)
							if (j2 > i1 || i2 < j1) {
								adj[k1][k2] = true;
								adj[k2][k1] = true;
							}
						if (i1 > j1 && i2 > j2)
							if ((i2 <= i1 && i2 > j1) || (i2 > j1 && j2 < i1)) {
								adj[k1][k2] = true;
								adj[k2][k1] = true;
							}
					}
				}
			}
		}

		// count the edges
		for (int i = 0; i < k; i++)
			for (int j = 0; j < i; j++)
				if (adj[i][j])
					m++;

		File lp_file = new File("../data/PartitionCol/instances/test/" + fileName);
		if (!lp_file.exists()) {
			lp_file.createNewFile();
		}
		FileWriter fw = new FileWriter(lp_file);
		BufferedWriter writer = new BufferedWriter(fw);
		// writer.newLine();
		writer.write(k + " " + m + " " + (k / 2));
		for (int i = 0; i < k / 2; i++) {
			writer.newLine();
			writer.write(i + "");
			writer.newLine();
			writer.write(i + "");
		}

		for (int i = 0; i < k; i++)
			for (int j = i + 1; j < k; j++)
				if (adj[i][j]) {
					writer.newLine();
					writer.write(i + " " + j);
				}
		if (writer != null)
			writer.close();
	}

	public static void generateRingInstNew(int n, double probability, String fileName) throws IOException {
		int k = 0, i1, i2, j1, j2, k1, k2, m = 0, sens1, sens2;
		ArrayList<Pair> listP = new ArrayList<Pair>();
		Pair newP1, newP2 = new Pair();
		Random rand = new Random();
		boolean[][] M = new boolean[n][n];
		for (int i = 0; i < n; i++)
			for (int j = 0; j < i; j++) {
				if (rand.nextDouble() <= probability) {
					M[i][j] = true;
					newP1 = new Pair(i, j, -1, -1, k);
					listP.add(newP1);
					k++;
					newP1 = new Pair(i, j, 1, 1, k);
					listP.add(newP1);
					k++;
				}
				if (rand.nextDouble() <= probability) {
					M[j][i] = true;
					newP1 = new Pair(j, i, -1, -1, k);
					listP.add(newP1);
					k++;
					newP1 = new Pair(j, i, 1, 1, k);
					listP.add(newP1);
					k++;
				}
			}

		boolean[][] adj = new boolean[k][k];
		Iterator<Pair> iter1 = listP.iterator();
		while (iter1.hasNext()) {
			newP1 = iter1.next();
			i1 = newP1.from;
			j1 = newP1.to;
			sens1 = newP1.fromId;
			k1 = newP1.node;
			Iterator<Pair> iter2 = listP.iterator();
			while (iter2.hasNext()) {
				newP2 = iter2.next();
				i2 = newP2.from;
				j2 = newP2.to;
				sens2 = newP2.fromId;
				k2 = newP2.node;
				if (k1 != k2) {
					if (sens1 == 1 && sens2 == 1) {
						if (i1 < j1 && i2 < j2)
							if (i2 < j1 && i1 < j2) {
								adj[k1][k2] = true;
								adj[k2][k1] = true;
							}
						if (i1 < j1 && i2 > j2)
							if (j1 > i2 || i1 < j2) {
								adj[k1][k2] = true;
								adj[k2][k1] = true;
							}
						if (i1 > j1 && i2 < j2)
							if (j2 > i1 || i2 < j1) {
								adj[k1][k2] = true;
								adj[k2][k1] = true;
							}
						if (i1 > j1 && i2 > j2) {
							adj[k1][k2] = true;
							adj[k2][k1] = true;
						}
					}
					if (sens1 == -1 && sens2 == -1) {
						if (i1 < j1 && i2 < j2) {
							adj[k1][k2] = true;
							adj[k2][k1] = true;
						}
						if (i1 < j1 && i2 > j2)
							if (j1 < i2 || i1 > j2) {
								adj[k1][k2] = true;
								adj[k2][k1] = true;
							}
						if (i1 > j1 && i2 < j2)
							if (j2 < i1 || i2 > j1) {
								adj[k1][k2] = true;
								adj[k2][k1] = true;
							}
						if (i1 > j1 && i2 > j2)
							if (j2 < i1 && i2 > j1) {
								adj[k1][k2] = true;
								adj[k2][k1] = true;
							}
					}
				}
			}
		}

		// count the edges
		for (int i = 0; i < k; i++)
			for (int j = 0; j < i; j++)
				if (adj[i][j])
					m++;

		File lp_file = new File("../data/PartitionCol/instances/test/" + fileName);
		if (!lp_file.exists()) {
			lp_file.createNewFile();
		}
		FileWriter fw = new FileWriter(lp_file);
		BufferedWriter writer = new BufferedWriter(fw);
		// writer.newLine();
		writer.write(k + " " + m + " " + (k / 2));
		for (int i = 0; i < k / 2; i++) {
			writer.newLine();
			writer.write(i + "");
			writer.newLine();
			writer.write(i + "");
		}

		for (int i = 0; i < k; i++)
			for (int j = i + 1; j < k; j++)
				if (adj[i][j]) {
					writer.newLine();
					writer.write(i + " " + j);
				}
		if (writer != null)
			writer.close();
	}

	public static void main(String[] args) throws IOException {
		int n = 50;
		double probability = 0.2;
		generateRingInstNew(n, probability, "ring_n" + n + "p" + probability + "s1.pcp");
		// generateRingInst(n, probability, "ring_n" + n + "p" + probability +
		// "s2.pcp");
		// generateRingInst(n, probability, "ring_n" + n + "p" + probability +
		// "s3.pcp");
		// generateRingInst(n, probability, "ring_n" + n + "p" + probability +
		// "s4.pcp");
		// generateRingInst(n, probability, "ring_n" + n + "p" + probability +
		// "s5.pcp");

		System.out.println("End generate");

	}
}