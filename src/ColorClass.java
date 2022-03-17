import java.util.HashSet;
import java.util.Iterator;
import java.util.Stack;

public class ColorClass {
	public HashSet<Integer> vertices;
	public double cost;
	public int size;
	public int id;

	public ColorClass() {
		this.vertices = new HashSet<Integer>();
		this.cost = -1;
		this.size = 0;
		this.id = -1;
	}

	public boolean check(ColorClass stableSet, int n) {
		int i;
		boolean[] currentSet = new boolean[n], newSet = new boolean[n];
		Iterator<Integer> iter1;
		if (this.vertices != null) {
			iter1 = this.vertices.iterator();
			while (iter1.hasNext()) {
				i = iter1.next().intValue();
				currentSet[i] = true;
			}
		}
		if (stableSet.vertices != null) {
			iter1 = stableSet.vertices.iterator();
			while (iter1.hasNext()) {
				i = iter1.next().intValue();
				newSet[i] = true;
			}
		}
		for (i = 0; i < n; i++)
			if (currentSet[i] != newSet[i])
				return false;

		return true;
	}

	public ColorClass(ColorClass colorClass) {
		this.vertices = new HashSet<Integer>();
		this.cost = -1;
		this.size = colorClass.vertices.size();

		Iterator<Integer> iterator = colorClass.vertices.iterator();
		if (colorClass != null)
			while (iterator.hasNext())
				this.vertices.add(iterator.next());
	}

	public ColorClass(HashSet<Integer> colorClass, boolean[][] adj) {
		this.vertices = colorClass;
		this.cost = 0;
		this.size = colorClass.size();

		Iterator<Integer> iter1, iter2;
		int i, j;

		if (colorClass != null) {
			iter1 = colorClass.iterator();
			while (iter1.hasNext()) {
				i = iter1.next().intValue();
				iter2 = colorClass.iterator();
				while (iter2.hasNext()) {
					j = iter2.next().intValue();
					if (j > i && adj[i][j]) {
						this.cost++;
					}
				}
			}
		}
	}

	public ColorClass(boolean[] characteristicSet) {
		this.vertices = new HashSet<Integer>();
		this.cost = -1;
		int n = characteristicSet.length;
		for (int h = 0; h < n; h++)
			if (characteristicSet[h])
				this.vertices.add(h);
		this.size = this.vertices.size();
	}

	public boolean isEqual(ColorClass colorClass, int n) {
		boolean result = true;
		boolean[] charactThis = new boolean[n];
		boolean[] charactThat = new boolean[n];
		int i;
		Iterator<Integer> iter = this.vertices.iterator();
		while (iter.hasNext()) {
			i = iter.next().intValue();
			charactThis[i] = true;
		}
		iter = colorClass.vertices.iterator();
		while (iter.hasNext()) {
			i = iter.next().intValue();
			charactThat[i] = true;
		}
		for (int j = 0; j < n; j++) {
			if (charactThis[j] != charactThat[j])
				return false;
		}
		return result;
	}

	public String toString() {
		String toStr = "";
		Iterator<Integer> iter;
		iter = this.vertices.iterator();
		while (iter.hasNext()) {
			toStr += " " + iter.next().intValue();
		}
		System.out.print(toStr + " | " + this.vertices.size());
		System.out.println();
		return toStr;
	}

}
