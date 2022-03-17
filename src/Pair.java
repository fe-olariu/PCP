import java.util.ArrayList;
import java.util.Iterator;

public class Pair {
	int from, to, fromId, toId, node;

	// if we contract the pair ("from", "to") then "node" will become the new
	// vertex;
	// if we add the edge between "from" and "to", then "node" will be -1;
	// "from" and "to" are the real names of the two vertices;
	// "fromId" and "toId" are their ordering numbers.

	Pair(int from, int to, int fromId, int toId, int node) {
		this.from = from;
		this.to = to;
		this.fromId = fromId;
		this.toId = toId;
		this.node = node;
	}

	Pair() {
		this.from = -1;
		this.to = -1;
		this.fromId = -1;
		this.toId = -1;
		this.node = -1;
	}
}
