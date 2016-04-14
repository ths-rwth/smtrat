/**
 * @file ConflictGraph.h
 * @ingroup cad
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include "../Common.h"

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

class SampleEvaluation {
private:
	IDPool mIDs;
	/// Stores for each constraints, which sample points violate the constraint.
	std::vector<Bitset> mData;
public:
	void addConstraint(std::size_t id) {
		if (id >= mData.size()) {
			mData.resize(id+1);
		}
	}
	void removeConstraint(std::size_t id) {
		assert(id < mData.size());
		if (id == mData.size()-1) {
			mData.pop_back();
		} else {
			mData[id] = Bitset();
		}
	}
	/**
	 * Registers a new sample point and returns its ID.
	 */
	std::size_t newSample() {
		return mIDs.get();
	}
	void set(std::size_t constraint, std::size_t sample, bool value) {
		if (constraint >= mData.size()) {
			mData.resize(constraint+1);
		}
		mData[constraint].set(sample, value);
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
	 * Removes the given constraint and disable all sample points covered by this constraint.
	 */
	void selectConstraint(std::size_t id) {
		assert(mData.size() > id);
		Bitset selection = mData[id];
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
	
	friend std::ostream& operator<<(std::ostream& os, const SampleEvaluation& cg) {
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
