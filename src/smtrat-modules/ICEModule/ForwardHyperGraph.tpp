namespace smtrat {
	
	template<typename VertexProperty, typename EdgeProperty, bool UniqueVertices>
	void ForwardHyperGraph<VertexProperty,EdgeProperty,UniqueVertices>::toDot(const std::string& filename) const {
		std::ofstream out(filename);
		out << "digraph G {" << std::endl;
		for (Vertex v = 0; v < mVertexProperties.size(); v++) {
			out << "\t" << v << " [label=\"" << mVertexProperties[v] << "\"];" << std::endl;
		}
		std::size_t edgeid = 0;
		for (Vertex src = 0; src < mEdges.size(); src++) {
			for (const auto& e: mEdges[src]) {
				out << "\tedge_" << edgeid << " [label=\"" << *e << "\", shape=box];" << std::endl;
				out << "\t" << src << " -> edge_" << edgeid << ";" << std::endl;
				for (const auto& dest: e.out()) {
					out << "\t" << "edge_" << edgeid << " -> " << dest << ";" << std::endl;
				}
				edgeid++;
			}
		}
		out << "}" << std::endl;
		out.close();
	}
	
	template<typename VP, typename EP, bool UV>
	std::ostream& operator<<(std::ostream& os, const ForwardHyperGraph<VP,EP,UV>& fhg) {
		os << "ForwardHyperGraph:" << std::endl;
		for (typename ForwardHyperGraph<VP,EP>::Vertex v = 0; v < fhg.mEdges.size(); v++) {
			os << "\t" << v << " (" << fhg.mVertexProperties[v] << ")" << std::endl;
			for (const auto& e: fhg.mEdges[v]) {
				os << "\t\t(" << *e << ") ->";
				for (const auto& out: e.out()) os << " " << out;
				os << std::endl;
			}
		}
		return os;
	}
	
/* ***** Pseudo-Code for the algorithm implemented below *****
block[v]: is vertex v blocked?
B[b]: list of vertices that are blocked due to vertex v
stack: vertices on the current path

function unblock(v):
	block[v] = false
	for u in B[v]: unblock(u)

function enumerate(src, v):
	found = false
	stack.push(v)
	block[v] = true
	for u in out(v):
		if u = src: output stack, found = true
		else if not block[u]:
			if enumerate(src, u): found = true
	if found: unblock(v)
	else:
		for u in out(v):
			add v to B[u]
	stack.pop()
	return found
			

function main:
	s = 1
	while s < n do
		look at subgraph induced by vertices s, ..., n
		unblock all vertices in subgraph
		find circuits starting from s: enumerate(s, s)
		s++
*/
	template<typename FHG, typename Collector>
	bool CycleEnumerator<FHG,Collector>::enumerate(CycleEnumerator<FHG,Collector>::Vertex src, CycleEnumerator<FHG,Collector>::Vertex v) {
		bool found = false;
		mVertexStack.push_back(v);
		mBlocked[v] = true;
		for (const auto& edge: mGraph.out(v)) {
			for (Vertex u: edge.out()) {
				if (u == src) {
					mEdgeStack.push_back(edge);
					mAborted = mCollector(mGraph, mVertexStack, mEdgeStack);
					if (mAborted) return false;
					found = true;
					mEdgeStack.pop_back();
				} else if (!mBlocked[u]) {
					mEdgeStack.push_back(edge);
					found = found || enumerate(src, u);
					if (mAborted) return false;
					mEdgeStack.pop_back();
				}
			}
		}
		if (found) unblock(v);
		else {
			for (const auto& edge: mGraph.out(v)) {
				for (Vertex u: edge.out()) {
					mBlockDependencies[u].push_back(v);
				}
			}
		}
		mVertexStack.pop_back();
		return found;
	}
		
	template<typename FHG, typename Collector>
	bool CycleEnumerator<FHG,Collector>::findAll() {
		mAborted = false;
		auto n = mGraph.begin();
		while (!mAborted && (n < mGraph.end())) {
			for (auto m = n; m < mGraph.end(); m++) unblock(m);
			for (auto m = mGraph.begin(); m < n; m++) mBlocked[m] = true;
			enumerate(n, n);
			n++;
		}
		return mAborted;
	}
	
}
