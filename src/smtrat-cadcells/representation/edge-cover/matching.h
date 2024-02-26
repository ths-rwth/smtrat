/**
 *
 * https://github.com/dilsonpereira/Minimum-Cost-Perfect-Matching
 *
 */

#pragma once

#include <smtrat-common/smtrat-common.h>

#include "graph.h"

namespace smtrat::cadcells::representation::util {

#define EPSILON 0.000001
#define GREATER(A, B) ((A) - (B) > EPSILON)

class Matching {
public:
	// Parametric constructor receives a graph instance
	Matching(const Graph& G);

	// Solves the minimum cost perfect matching problem
	// Receives the a vector whose position i has the cost of the edge with index i
	// If the graph doest not have a perfect matching, a const char * exception will be raised
	// Returns a pair
	// the first element of the pair is a list of the indices of the edges in the matching
	// the second is the cost of the matching
	std::pair<std::vector<Graph::edge_descriptor>, double> SolveMinimumCostPerfectMatching();

private:
	// Solves the maximum cardinality matching problem
	// Returns a list with the indices of the edges in the matching
	std::vector<Graph::edge_descriptor> SolveMaximumMatching();

	// Grows an alternating forest
	void Grow();

	// Expands a blossom u
	// If expandBlocked is true, the blossom will be expanded even if it is blocked
	void Expand(int u, bool expandBlocked);

	// Augments the matching using the path from u to v in the alternating forest
	void Augment(int u, int v);

	// Resets the alternating forest
	void Reset();

	// Creates a blossom where the tip is the first common vertex in the paths from u and v in the hungarian forest
	int Blossom(int u, int v);

	void UpdateDualCosts();

	// Resets all data structures
	void Clear();

	void DestroyBlossom(int t);

	// Uses an heuristic algorithm to find the maximum matching of the graph
	void Heuristic();

	// Modifies the costs of the graph so the all edges have positive costs
	void PositiveCosts();

	std::vector<Graph::edge_descriptor> RetrieveMatching();

	int GetFreeBlossomIndex();
	void AddFreeBlossomIndex(int i);
	void ClearBlossomIndices();

	// An edge might be blocked due to the dual costs
	bool IsEdgeBlocked(int u, int v);
	bool IsEdgeBlocked(int e);

	// Returns true if u and v are adjacent in G and not blocked
	bool IsAdjacent(int u, int v);

	const Graph& G;

	std::list<int> free; // List of free blossom indices

	std::vector<int> outer;				 // outer[v] gives the index of the outermost blossom that contains v, outer[v] = v if v is not contained in any blossom
	std::vector<std::list<int>> deep;	 // deep[v] is a list of all the original vertices contained inside v, deep[v] = v if v is an original vertex
	std::vector<std::list<int>> shallow; // shallow[v] is a list of the vertices immediately contained inside v, shallow[v] is empty is the default
	std::vector<int> tip;				 // tip[v] is the tip of blossom v
	std::vector<bool> active;			 // true if a blossom is being used

	std::vector<int> type;	 // Even, odd, neither (2, 1, 0)
	std::vector<int> forest; // forest[v] gives the father of v in the alternating forest
	std::vector<int> root;	 // root[v] gives the root of v in the alternating forest

	std::vector<bool> blocked; // A blossom can be blocked due to dual costs, this means that it behaves as if it were an original vertex and cannot be expanded
	std::vector<double> dual;  // dual multipliers associated to the blossoms, if dual[v] > 0, the blossom is blocked and full
	std::vector<double> slack; // slack associated to each edge, if slack[e] > 0, the edge cannot be used
	std::vector<int> mate;	   // mate[v] gives the mate of v

	int m, n;

	bool perfect;

	std::list<int> forestList;
	std::vector<int> visited;
};

inline Matching::Matching(const Graph& G)
	: G(G),
	  outer(2 * boost::num_vertices(G)),
	  deep(2 * boost::num_vertices(G)),
	  shallow(2 * boost::num_vertices(G)),
	  tip(2 * boost::num_vertices(G)),
	  active(2 * boost::num_vertices(G)),
	  type(2 * boost::num_vertices(G)),
	  forest(2 * boost::num_vertices(G)),
	  root(2 * boost::num_vertices(G)),
	  blocked(2 * boost::num_vertices(G)),
	  dual(2 * boost::num_vertices(G)),
	  slack(boost::num_edges(G)),
	  mate(2 * boost::num_vertices(G)),
	  m(boost::num_edges(G)),
	  n(boost::num_vertices(G)),
	  visited(2 * boost::num_vertices(G)) {
}

inline void Matching::Grow() {
	Reset();

	// All unmatched vertices will be roots in a forest that will be grown
	// The forest is grown by extending a unmatched vertex w through a matched edge u-v in a BFS fashion
	while (!forestList.empty()) {
		int w = outer[forestList.front()];
		forestList.pop_front();

		// w might be a blossom
		// we have to explore all the connections from vertices inside the blossom to other vertices
		for (auto it = deep[w].begin(); it != deep[w].end(); it++) {
			int u = *it;

			int cont = false;
			for (const auto& v : boost::make_iterator_range(boost::adjacent_vertices(u, G))) {
				if (IsEdgeBlocked(u, v)) {
					continue;
				}

				// u is even and v is odd
				if (type[outer[v]] == 1) {
					continue;
				}

				// if v is unlabeled
				if (type[outer[v]] != 2) {
					// We grow the alternating forest
					int vm = mate[outer[v]];

					forest[outer[v]] = u;
					type[outer[v]] = 1;
					root[outer[v]] = root[outer[u]];
					forest[outer[vm]] = v;
					type[outer[vm]] = 2;
					root[outer[vm]] = root[outer[u]];

					if (!visited[outer[vm]]) {
						forestList.push_back(vm);
						visited[outer[vm]] = true;
					}
				}
				// If v is even and u and v are on different trees
				// we found an augmenting path
				else if (root[outer[v]] != root[outer[u]]) {
					Augment(u, v);
					Reset();

					cont = true;
					break;
				}
				// If u and v are even and on the same tree
				// we found a blossom
				else if (outer[u] != outer[v]) {
					int b = Blossom(u, v);

					forestList.push_front(b);
					visited[b] = true;

					cont = true;
					break;
				}
			}
			if (cont) {
				break;
			}
		}
	}

	// Check whether the matching is perfect
	perfect = true;
	for (int i = 0; i < n; i++) {
		if (mate[outer[i]] == -1) {
			perfect = false;
		}
	}
}

inline bool Matching::IsAdjacent(int u, int v) {
	return (boost::edge(u, v, G).second && !IsEdgeBlocked(u, v));
}

inline bool Matching::IsEdgeBlocked(int u, int v) {
	auto edge = boost::edge(u, v, G).first;
	return GREATER(slack[boost::get(boost::edge_index, G, edge)], 0);
}

inline bool Matching::IsEdgeBlocked(int e) {
	return GREATER(slack[e], 0);
}

// Vertices will be selected in non-decreasing order of their degree
// Each time an unmatched vertex is selected, it is matched to its adjacent unmatched vertex of minimum degree
inline void Matching::Heuristic() {
	std::vector<int> degree(n, 0);

	for (const auto& edge : boost::make_iterator_range(boost::edges(G))) {
		int u = boost::source(edge, G);
		int v = boost::target(edge, G);

		if (IsEdgeBlocked(u, v)) {
			continue;
		}

		degree[u]++;
		degree[v]++;
	}

	using ValueKeyPair = std::pair<double, int>;
	std::priority_queue<ValueKeyPair, std::vector<ValueKeyPair>, std::greater<ValueKeyPair>> heap;

	for (int i = 0; i < n; i++) {
		heap.push(std::make_pair(degree[i], i));
	}

	while (heap.size() > 0) {
		int u = heap.top().second;
		heap.pop();
		if (mate[outer[u]] == -1) {
			int min = -1;

			for (const auto& v : boost::make_iterator_range(boost::adjacent_vertices(u, G))) {
				if (IsEdgeBlocked(u, v) || outer[u] == outer[v] || mate[outer[v]] != -1) {
					continue;
				}

				if (min == -1 || degree[v] < degree[min]) {
					min = v;
				}
			}

			if (min != -1) {
				mate[outer[u]] = min;
				mate[outer[min]] = u;
			}
		}
	}
}

// Destroys a blossom recursively
inline void Matching::DestroyBlossom(int t) {
	if ((t < n) || (blocked[t] && GREATER(dual[t], 0))) {
		return;
	}

	for (auto it = shallow[t].begin(); it != shallow[t].end(); it++) {
		int s = *it;
		outer[s] = s;
		for (auto jt = deep[s].begin(); jt != deep[s].end(); jt++) {
			outer[*jt] = s;
		}

		DestroyBlossom(s);
	}

	active[t] = false;
	blocked[t] = false;
	AddFreeBlossomIndex(t);
	mate[t] = -1;
}

inline void Matching::Expand(int u, bool expandBlocked = false) {
	int v = outer[mate[u]];

	int index = m;
	int p = -1, q = -1;
	// Find the regular edge {p,q} of minimum index connecting u and its mate
	// We use the minimum index to grant that the two possible blossoms u and v will use the same edge for a mate
	for (auto it = deep[u].begin(); it != deep[u].end(); it++) {
		int di = *it;
		for (auto jt = deep[v].begin(); jt != deep[v].end(); jt++) {
			int dj = *jt;

			auto [edge, exists] = boost::edge(di, dj, G);
			if (!exists) {
				continue;
			}

			int edge_index = boost::get(boost::edge_index, G, edge);
			if (IsAdjacent(di, dj) && edge_index < index) {
				index = edge_index;
				p = di;
				q = dj;
			}
		}
	}

	mate[u] = q;
	mate[v] = p;
	// If u is a regular vertex, we are done
	if (u < n || (blocked[u] && !expandBlocked)) {
		return;
	}

	bool found = false;
	// Find the position t of the new tip of the blossom
	for (auto it = shallow[u].begin(); it != shallow[u].end() && !found;) {
		int si = *it;
		for (auto jt = deep[si].begin(); jt != deep[si].end() && !found; jt++) {
			if (*jt == p) {
				found = true;
			}
		}
		it++;
		if (!found) {
			shallow[u].push_back(si);
			shallow[u].pop_front();
		}
	}

	auto it = shallow[u].begin();
	// Adjust the mate of the tip
	mate[*it] = mate[u];
	it++;
	//
	// Now we go through the odd circuit adjusting the new mates
	while (it != shallow[u].end()) {
		auto itnext = it;
		itnext++;
		mate[*it] = *itnext;
		mate[*itnext] = *it;
		itnext++;
		it = itnext;
	}

	// We update the sets blossom, shallow, and outer since this blossom is being deactivated
	for (auto it = shallow[u].begin(); it != shallow[u].end(); it++) {
		int s = *it;
		outer[s] = s;
		for (auto jt = deep[s].begin(); jt != deep[s].end(); jt++) {
			outer[*jt] = s;
		}
	}
	active[u] = false;
	AddFreeBlossomIndex(u);

	// Expand the vertices in the blossom
	for (auto it = shallow[u].begin(); it != shallow[u].end(); it++) {
		Expand(*it, expandBlocked);
	}
}

// Augment the path root[u], ..., u, v, ..., root[v]
inline void Matching::Augment(int u, int v) {
	// We go from u and v to its respective roots, alternating the matching
	int p = outer[u];
	int q = outer[v];
	int outv = q;
	int fp = forest[p];
	mate[p] = q;
	mate[q] = p;
	Expand(p);
	Expand(q);
	while (fp != -1) {
		q = outer[forest[p]];
		p = outer[forest[q]];
		fp = forest[p];

		mate[p] = q;
		mate[q] = p;
		Expand(p);
		Expand(q);
	}

	p = outv;
	fp = forest[p];
	while (fp != -1) {
		q = outer[forest[p]];
		p = outer[forest[q]];
		fp = forest[p];

		mate[p] = q;
		mate[q] = p;
		Expand(p);
		Expand(q);
	}
}

inline void Matching::Reset() {
	for (int i = 0; i < 2 * n; i++) {
		forest[i] = -1;
		root[i] = i;

		if (i >= n && active[i] && outer[i] == i) {
			DestroyBlossom(i);
		}
	}

	visited.assign(2 * n, 0);
	forestList.clear();
	for (int i = 0; i < n; i++) {
		if (mate[outer[i]] == -1) {
			type[outer[i]] = 2;
			if (!visited[outer[i]]) {
				forestList.push_back(i);
			}
			visited[outer[i]] = true;
		} else {
			type[outer[i]] = 0;
		}
	}
}

inline int Matching::GetFreeBlossomIndex() {
	int i = free.back();
	free.pop_back();
	return i;
}

inline void Matching::AddFreeBlossomIndex(int i) {
	free.push_back(i);
}

inline void Matching::ClearBlossomIndices() {
	free.clear();
	for (int i = n; i < 2 * n; i++) {
		AddFreeBlossomIndex(i);
	}
}

// Contracts the blossom w, ..., u, v, ..., w, where w is the first vertex that appears in the paths from u and v to their respective roots
inline int Matching::Blossom(int u, int v) {
	int t = GetFreeBlossomIndex();

	std::vector<bool> isInPath(2 * n, false);

	// Find the tip of the blossom
	int u_ = u;
	while (u_ != -1) {
		isInPath[outer[u_]] = true;

		u_ = forest[outer[u_]];
	}

	int v_ = outer[v];
	while (!isInPath[v_]) {
		v_ = outer[forest[v_]];
	}
	tip[t] = v_;

	// Find the odd circuit, update shallow, outer, blossom and deep
	// First we construct the set shallow (the odd circuit)
	std::list<int> circuit;
	u_ = outer[u];
	circuit.push_front(u_);
	while (u_ != tip[t]) {
		u_ = outer[forest[u_]];
		circuit.push_front(u_);
	}

	shallow[t].clear();
	deep[t].clear();
	for (auto it = circuit.begin(); it != circuit.end(); it++) {
		shallow[t].push_back(*it);
	}

	v_ = outer[v];
	while (v_ != tip[t]) {
		shallow[t].push_back(v_);
		v_ = outer[forest[v_]];
	}

	// Now we construct deep and update outer
	for (auto it = shallow[t].begin(); it != shallow[t].end(); it++) {
		u_ = *it;
		outer[u_] = t;
		for (auto jt = deep[u_].begin(); jt != deep[u_].end(); jt++) {
			deep[t].push_back(*jt);
			outer[*jt] = t;
		}
	}

	forest[t] = forest[tip[t]];
	type[t] = 2;
	root[t] = root[tip[t]];
	active[t] = true;
	outer[t] = t;
	mate[t] = mate[tip[t]];

	return t;
}

inline void Matching::UpdateDualCosts() {
	double e1 = 0, e2 = 0, e3 = 0;
	int inite1 = false, inite2 = false, inite3 = false;
	for (auto [it, i] = std::tuple(boost::edges(G), 0); it.first != it.second && i < m; it.first++, ++i) {
		int u = boost::source(*it.first, G);
		int v = boost::target(*it.first, G);

		if ((type[outer[u]] == 2 && type[outer[v]] == 0) || (type[outer[v]] == 2 && type[outer[u]] == 0)) {
			if (!inite1 || GREATER(e1, slack[i])) {
				e1 = slack[i];
				inite1 = true;
			}
		} else if ((outer[u] != outer[v]) && type[outer[u]] == 2 && type[outer[v]] == 2) {
			if (!inite2 || GREATER(e2, slack[i])) {
				e2 = slack[i];
				inite2 = true;
			}
		}
	}
	for (int i = n; i < 2 * n; i++) {
		if (active[i] && i == outer[i] && type[outer[i]] == 1 && (!inite3 || GREATER(e3, dual[i]))) {
			e3 = dual[i];
			inite3 = true;
		}
	}
	double e = 0;
	if (inite1) {
		e = e1;
	} else if (inite2) {
		e = e2;
	} else if (inite3) {
		e = e3;
	}

	if (GREATER(e, e2 / 2.0) && inite2) {
		e = e2 / 2.0;
	}
	if (GREATER(e, e3) && inite3) {
		e = e3;
	}

	for (int i = 0; i < 2 * n; i++) {
		if (i != outer[i]) {
			continue;
		}

		if (active[i] && type[outer[i]] == 2) {
			dual[i] += e;
		} else if (active[i] && type[outer[i]] == 1) {
			dual[i] -= e;
		}
	}

	for (auto [it, i] = std::tuple(boost::edges(G), 0); it.first != it.second && i < m; it.first++, ++i) {
		int u = boost::source(*it.first, G);
		int v = boost::target(*it.first, G);

		if (outer[u] != outer[v]) {
			if (type[outer[u]] == 2 && type[outer[v]] == 2) {
				slack[i] -= 2.0 * e;
			} else if (type[outer[u]] == 1 && type[outer[v]] == 1) {
				slack[i] += 2.0 * e;
			} else if ((type[outer[v]] == 0 && type[outer[u]] == 2) || (type[outer[u]] == 0 && type[outer[v]] == 2)) {
				slack[i] -= e;
			} else if ((type[outer[v]] == 0 && type[outer[u]] == 1) || (type[outer[u]] == 0 && type[outer[v]] == 1)) {
				slack[i] += e;
			}
		}
	}

	for (int i = n; i < 2 * n; i++) {
		if (GREATER(dual[i], 0)) {
			blocked[i] = true;
		} else if (active[i] && blocked[i]) {
			// The blossom is becoming unblocked
			if (mate[i] == -1) {
				DestroyBlossom(i);
			} else {
				blocked[i] = false;
				Expand(i);
			}
		}
	}
}

inline std::pair<std::vector<Graph::edge_descriptor>, double> Matching::SolveMinimumCostPerfectMatching() {
	SolveMaximumMatching();
	if (!perfect) {
		SMTRAT_LOG_ERROR("smtrat.cadcells.representation", "Error: The graph does not have a perfect matching");
	}

	Clear();

	// Initialize slacks (reduced costs for the edges)
	for (const auto& edge : boost::make_iterator_range(boost::edges(G))) {
		int u = boost::source(edge, G);
		int v = boost::target(edge, G);

		// get index
		int idx = boost::get(boost::edge_index, G, edge);

		slack[idx] = boost::get(boost::edge_weight, G, edge);
	}

	PositiveCosts();

	// If the matching on the compressed graph is perfect, we are done
	perfect = false;
	while (!perfect) {
		// Run an heuristic maximum matching algorithm
		Heuristic();
		// Grow a hungarian forest
		Grow();
		UpdateDualCosts();
		// Set up the algorithm for a new grow step
		Reset();
	}

	std::vector<Graph::edge_descriptor> matching = RetrieveMatching();

	double obj = 0;
	for (auto it = matching.begin(); it != matching.end(); it++) {
		obj += boost::get(boost::edge_weight, G, *it);
	}

	return std::pair<std::vector<Graph::edge_descriptor>, double>(matching, obj);
}

inline void Matching::PositiveCosts() {
	double minEdge = 0;
	for (int i = 0; i < m; i++) {
		if (GREATER(minEdge - slack[i], 0)) {
			minEdge = slack[i];
		}
	}

	for (int i = 0; i < m; i++) {
		slack[i] -= minEdge;
	}
}

inline std::vector<Graph::edge_descriptor> Matching::SolveMaximumMatching() {
	Clear();
	Grow();
	return RetrieveMatching();
}

// Sets up the algorithm for a new run
inline void Matching::Clear() {
	ClearBlossomIndices();

	for (int i = 0; i < 2 * n; i++) {
		outer[i] = i;
		deep[i].clear();
		if (i < n) {
			deep[i].push_back(i);
		}
		shallow[i].clear();
		if (i < n) {
			active[i] = true;
		} else {
			active[i] = false;
		}

		type[i] = 0;
		forest[i] = -1;
		root[i] = i;

		blocked[i] = false;
		dual[i] = 0;
		mate[i] = -1;
		tip[i] = i;
	}
	slack.assign(m, 0);
}

inline std::vector<Graph::edge_descriptor> Matching::RetrieveMatching() {
	std::vector<Graph::edge_descriptor> matching;

	for (int i = 0; i < 2 * n; i++) {
		if (active[i] && mate[i] != -1 && outer[i] == i) {
			Expand(i, true);
		}
	}

	for (const auto& edge : boost::make_iterator_range(boost::edges(G))) {
		int u = boost::source(edge, G);
		int v = boost::target(edge, G);

		if (mate[u] == v) {
			matching.push_back(edge);
		}
	}

	return matching;
}

} // namespace smtrat::cadcells::representation::util
