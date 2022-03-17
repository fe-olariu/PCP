import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;

public class ReadGraphFromFile {

	public ReadGraphFromFile() {
	}

	public static int[] readGraphSize(String dataFile) {
		int[] size = new int[3];
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

	public static int[] readGraph(String dataFile, boolean[][] adjacency, int[] clusters,
			ColorClass[] clustersContent) {
		int[] size = readGraphSize(dataFile);
		int h, l;
		ColorClass _class;
		String path = "../data/PartitionCol/", text = null;
		File file = new File(path + "instances/" + dataFile);
		BufferedReader reader = null;
		String[] nors = null;
		try {
			reader = new BufferedReader(new FileReader(file));
			text = reader.readLine();
			for (int i = 0; i < size[0]; i++) {
				if ((text = reader.readLine()) != null) {
					h = Integer.valueOf(text);
					clusters[i] = h;
					if (clustersContent[h] == null)
						clustersContent[h] = new ColorClass();
					clustersContent[h].vertices.add((Integer) i);
				}
			}
			while ((text = reader.readLine()) != null) {
				nors = text.split("\\s+", 0);
				h = Integer.valueOf(nors[0]);
				l = Integer.valueOf(nors[1]);
				adjacency[h][l] = true;
				adjacency[l][h] = true;
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return size;
	}

	public static void readFile(String dataFile) {
		int[] size = readGraphSize(dataFile);
		int n = size[0], k = size[2];
		boolean[][] adj = new boolean[n][n];
		int[] cluster = new int[n];
		ColorClass[] clusterContent = new ColorClass[k];
		readGraph(dataFile, adj, cluster, clusterContent);
	}

	public static void main(String[] args) {
		int[] size = readGraphSize("nsf_p0.9_s3.pcp");
		int n = size[0], m = size[1];
		readFile("nsf_p0.9_s3.pcp");
		System.out.println("n = " + n + "; m = " + m);
		System.out.println("End");

	}
}
