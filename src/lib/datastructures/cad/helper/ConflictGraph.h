/**
 * @file ConflictGraph.h
 * @ingroup cad
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include "../lifting/Sample.h"

#include <iostream>
#include <vector>

namespace smtrat {
namespace cad {

/**
 * Representation of a bipartite graph (C+S, E) of vertices C and S, representing the constraints and samples, respectively.
 *
 * A vertex from C and a vertex from S are connected by an edge in E iff the corresponding constraint conflicts with the corresponding sample point.
 */

class ConflictGraph {
public:
	friend std::ostream& operator<<(std::ostream& os, const ConflictGraph& cg);
private:
	/// Stores for each constraints, which sample points violate the constraint.
	std::vector<carl::Bitset> mData;
	std::size_t mNextSID = 0;
public:
	ConflictGraph(std::size_t constraints): mData(constraints) {}
	std::size_t coveredSamples(std::size_t id) const {
		return mData[id].count();
	}
	void addSample(const Sample& sample);

	/**
	 * Retrieves the constraint that covers the most samples.
	 */
	std::size_t getMaxDegreeConstraint() const;

	/**
	 * Removes the given constraint and disable all sample points covered by this constraint.
	 */
	void selectConstraint(std::size_t id);
	
	/**
	 * Selects all essential constraints and
	 * returns their indices
	 */
	std::vector<size_t> selectEssentialConstraints();
	
	/**
	 * Returns a new ConflictGraph whose adjacency matrix consists 
	 * only of the unique columns of the adjacency matrix of this graph.
	 */
	ConflictGraph removeDuplicateColumns();
	
	/**
	 * Checks if there are samples still uncovered.
	 */
	bool hasRemainingSamples() const;
	
	std::size_t numSamples() const;
	
	std::size_t numRemainingConstraints() const;
	
	carl::Bitset getData(std::size_t id);
	
	std::vector<std::pair<std::size_t, carl::Bitset>> getRemainingConstraints();
	
};

std::ostream& operator<<(std::ostream& os, const ConflictGraph& cg);

}
}
