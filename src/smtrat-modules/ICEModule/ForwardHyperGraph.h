#pragma once

#include <fstream>
#include <iostream>
#include <map>
#include <vector>

namespace smtrat {

/**
 * This class implements a forward hypergraph.
 *
 * We define a hypergraph to be a graph structure $(V,E)$ where $V$ is a set of vertices and $E \subseteq 2^V$ a set of hyperedges.
 * A hyperedge can connect an arbitrary number of vertices.
 *
 * If a hypergraph is directed if every edge $e \in E$ is partitioned into $I(e)$ and $O(e)$ that are sets of incoming vertices and outgoing vertices, respectively.
 * A forward hypergraph is directed and every edge has only a single incoming vertices, that is $|I(e)| = 1$.
 * Note that we store edges as a mapping from the incoming vertex to a set of outgoing vertices and thus do not have an explicit incoming vertex in our edge representation.
 *
 * This implementation of a forward hypergraph accepts arbitrary labels (called properties) for both vertices and edges.
 * It relies on a dense list of vertices that are internally labeled starting from zero.
 * Therefore, removal of vertices is not supported.
 *
 * If the third template parameter UniqueVertices is set to true (being the default), we make sure that every vertex is unique with respect to its property.
 * To make this possible, a vertex property may not be changed in this case which is enforced using a static assertion.
 * No requirements are imposed on the edge properties.
 *
 * This class supports both printing a simple text representation and writing a description to a dot file.
 */
template<typename VertexProperty, typename EdgeProperty, bool UniqueVertices = true>
class ForwardHyperGraph {
public:
	/// Internal type of a vertex.
	using Vertex = std::size_t;
	/// Internal type of an edge.
	struct Edge {
		friend ForwardHyperGraph;
	private:
		/// Property of this edge.
		EdgeProperty mProperty;
		/// Outgoing vertices.
		std::vector<Vertex> mOut;
	public:
		/// Constructor from a property.
		Edge(const EdgeProperty& ep): mProperty(ep), mOut() {}
		/// Add v to the outgoing vertices of this edge.
		void addOut(Vertex v) {
			mOut.emplace_back(v);
		}
		/// Access the property.
		const EdgeProperty& operator*() const {
			return mProperty;
		}
		/// Access the property.
		EdgeProperty& operator*() {
			return mProperty;
		}
		/// Access the property.
		const EdgeProperty* operator->() const {
			return &mProperty;
		}
		/// Access the property.
		EdgeProperty* operator->() {
			return &mProperty;
		}
		/// Retrieve the list of outgoing vertices.
		const std::vector<Vertex>& out() const {
			return mOut;
		}
	};
private:
	/// Storage for all vertex properties.
	std::vector<VertexProperty> mVertexProperties;
	/// Mapping from vertices to outgoing edges.
	std::vector<std::vector<Edge>> mEdges;
	/// Mapping from vertex properties to vertices to ensure uniqueness.
	std::map<VertexProperty,Vertex> mVertexMap;
public:
	/// Returns a new vertex that is labeled with the given vertex property.
	/// If UniqueVertices is set to true and a vector with the given property already exists, this vector is returned.
	Vertex newVertex(const VertexProperty& vp) {
		if (UniqueVertices) {
			auto it = mVertexMap.find(vp);
			if (it != mVertexMap.end()) return it->second;
			mVertexMap.emplace(vp, mEdges.size());
		}
		mEdges.emplace_back();
		mVertexProperties.emplace_back(vp);
		return mEdges.size() - 1;
	}
	/// Creates a new edge where the given vertex is the incoming vertex that is labeled with the given edge property.
	Edge& newEdge(Vertex source, const EdgeProperty& ep) {
		assert(source < mEdges.size());
		mEdges[source].emplace_back(ep);
		return mEdges[source].back();
	}
	/// Creates a new edge where the given vertex is the incoming vertex that is labeled with the given edge property.
	Edge& newEdge(const VertexProperty& source, const EdgeProperty& ep) {
		return newEdge(getVertex(source), ep);
	}
	
	/// Retrieves the vertex property for the given vertex.
	const VertexProperty& operator[](Vertex v) const {
		return mVertexProperties[v];
	}
	/// Retrieves the vertex property for the given vertex.
	/// This method is disabled if UniqueVertices is set to true.
	VertexProperty& operator[](Vertex v) {
		static_assert(!UniqueVertices, "Non-const references to vertex properties are not supported if UniqueVertices is set to true.");
		return mVertexProperties[v];
	}
	
	/// Retrieves all outgoing edges for the given vertex.
	const std::vector<Edge>& out(Vertex v) const {
		return mEdges[v];
	}
	/// Retrieves all outgoing edges for the given vertex.
	const std::vector<Edge>& out(const VertexProperty& v) const {
		return mEdges[getVertex(v)];
	}
	/// Returns the first vertex.
	Vertex begin() const {
		return 0;
	}
	/// Returns the past-the-last vertex.
	Vertex end() const {
		return mVertexProperties.size();
	}
	/// Returns the number of vertices.
	std::size_t size() const {
		return mVertexProperties.size();
	}
	/// Writes a representation of this graph to the given file.
	void toDot(const std::string& filename) const;
	
	/// Writes a textual representation of this graph to the given stream.
	template<typename VP, typename EP>
	friend std::ostream& operator<<(std::ostream& os, const ForwardHyperGraph<VP,EP>& fhg);
};

/**
 * This class encapsulates an algorithm for enumerating all cycles.
 *
 * This class implements an adaption of the algorithm described in @cite Johnson75.
 * Unlike the algorithm described there, this version works on forward hypergraphs as implemented by ForwardHyperGraph.
 *
 * Although the algorithm works recursively, this implementation can be used somewhat iteratively.
 * The cycles are given to the caller using an collector functor. If this functor returns true, the search for more cycles is aborted immediately.
 * Due to this pattern, there is no need to store the cycles within this class and thus the memory usage is minimized.
 */
template<typename FHG, typename Collector>
struct CycleEnumerator {
private:
	/// Type of a vertex.
	using Vertex = typename FHG::Vertex;
	/// Reference to the graph we search cycles in.
	const FHG& mGraph;
	
	/// Stores whether a vector is currently blocked.
	std::vector<bool> mBlocked;
	/// Stores vertex dependencies when vertices are blocked.
	std::vector<std::vector<Vertex>> mBlockDependencies;
	/// Stores the current list of vertices.
	std::vector<typename FHG::Vertex> mVertexStack;
	/// Stores the current list of edges.
	std::vector<typename FHG::Edge> mEdgeStack;
	/// The callback object.
	Collector& mCollector;
	/// Whether this search has been aborted by the collector.
	bool mAborted;
public:
	/// Constructor from a graph and a collector object.
	CycleEnumerator(const FHG& fhg, Collector& c):
		mGraph(fhg),
		mBlocked(fhg.size(), false),
		mBlockDependencies(fhg.size()),
		mVertexStack(),
		mEdgeStack(),
		mCollector(c),
		mAborted(false)
	{}
	/// Start the search for all cycles. Returns whether the search was finished (true) or aborted (false).
	bool findAll();
	
private:
	/// Unblocks the given vertex and all vertices that depend on it.
	void unblock(Vertex v) {
		if (!mBlocked[v]) return;
		mBlocked[v] = false;
		for (auto u: mBlockDependencies[v]) unblock(u);
		mBlockDependencies[v].clear();
	}
	/// Recursively enumerate all cycles that start in src and are currently in v.
	bool enumerate(Vertex src, Vertex v);
};

}

#include "ForwardHyperGraph.tpp"
