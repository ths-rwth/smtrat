/**
 * @file ConflictGraph.h
 * @ingroup cad
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include "../Common.h"
#include "../lifting/Sample.h"

#include <iostream>
#include <map>
#include <vector>

namespace smtrat {
namespace cad {

/**
 * Representation of a bipartite graph (C+S, E) of vertices C and S, representing the constraints and samples, respectively.
 *
 * A vertex from C and a vertex from S are connected by an edge in E iff the corresponding constraint conflicts with the corresponding sample point.
 */

class ConflictGraph {
private:
	/// Stores for each constraints, which sample points violate the constraint.
	std::vector<carl::Bitset> mData;
	std::size_t mNextSID = 0;
public:
	ConflictGraph(std::size_t constraints): mData(constraints) {}
	std::size_t coveredSamples(std::size_t id) const {
		return mData[id].count();
	}
	void addSample(const Sample& sample) {
		assert(sample.hasConflictWithConstraint());
		std::size_t sid = mNextSID++;
		const carl::Bitset& evalWith = sample.evaluatedWith();
		for (std::size_t pos = evalWith.find_first(); pos != carl::Bitset::npos; pos = evalWith.find_next(pos)) {
			if (!sample.evaluationResult().test(pos)) {
				mData[pos].set(sid, true);
			}
		}
	}
	/**
	 * Retrieves the constraint that covers the most samples.
	 */
	std::size_t getMaxDegreeConstraint() const {
		assert(mData.size() > 0);
		std::size_t maxID = 0;
		std::size_t maxDegree = 0;
		for (std::size_t id = 0; id < mData.size(); id++) {
			std::size_t deg = mData[id].count();
			if (deg > maxDegree) {
				maxDegree = deg;
				maxID = id;
			}
		}
		return maxID;
	}

	/**
	 * Disables all sample points that violate a superset of the constraints another sample violates.
	 */
	void disableSupersets(){
		// std::sort(mData.begin(), mData.end());
		/*
		for (std::size_t id = 0; id < mData.size(); id++) {
			for (std::size_t next = 0; next < mData.size(); next++) {
				if (id == next){
					continue;
				}
				if (mData[id].is_subset_of(mData[next])){
					this->selectConstraint(id);
				}
			}
		}*/
	}

	/**
	 * Removes the given constraint and disable all sample points covered by this constraint.
	 */
	void selectConstraint(std::size_t id) {
		assert(mData.size() > id);
		carl::Bitset selection = mData[id];
		for (auto& d: mData) d -= mData[id];
	}
	/**
	 * Checks if there are samples still uncovered.
	 */
	bool hasRemainingSamples() const {
		for (const auto& d: mData) {
			if (d.any()) return true;
		}
		return false;
	}
	
	std::size_t getDegree(std::size_t id){
		return mData[id].count();
	}
	
	friend std::ostream& operator<<(std::ostream& os, const ConflictGraph& cg) {
		os << "Print CG with " << cg.mData.size() << " constraints" << std::endl;
		for (std::size_t i = 0; i < cg.mData.size(); i++) {
			os << i << ":" << std::endl;
			os << "\t" << cg.mData[i] << std::endl;
		}
		return os;
	}
};

}
}
