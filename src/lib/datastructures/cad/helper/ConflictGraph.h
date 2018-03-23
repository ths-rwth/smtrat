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
	 * Removes the given constraint and disable all sample points covered by this constraint.
	 */
	void selectConstraint(std::size_t id) {
		assert(mData.size() > id);
		carl::Bitset selection = mData[id];
		for (auto& d: mData){
			d -= selection;
		}
	}
	
	/**
	 * Selects all essential constraints and
	 * returns their indices
	 */
	std::vector<size_t> selectEssentialConstraints(){
		std::vector<size_t> res;
		for (size_t sample = 0; sample < numSamples(); sample++){
			size_t numConflicts = 0;
			size_t essentialConstraint = 0;
			for(size_t constraint = 0; constraint < mData.size(); constraint++){
				if(mData[constraint].test(sample)) {
					numConflicts++;
					essentialConstraint = constraint;
				}
			}
			if(numConflicts == 1){
				selectConstraint(essentialConstraint);
				res.push_back(essentialConstraint);
			}
		}
		return res;
	}
	
	/**
	 * Returns a new ConflictGraph whose adjacency matrix consists 
	 * only of the unique columns of the adjacency matrix of this graph.
	 */
	ConflictGraph removeDuplicateColumns(){
		std::set<std::vector<uint8_t>> uniqueColumns;
		for(size_t s = 0; s < numSamples(); s++){
			std::vector<uint8_t> column (mData.size(), 0);
			for(size_t constraint = 0; constraint < mData.size(); constraint++){
				column[constraint] = mData[constraint].test(s);
			}
			uniqueColumns.insert(column);
		}
		ConflictGraph res(mData.size());
		for(auto& b : res.mData){
			b.resize(uniqueColumns.size());
		}
		size_t sid = 0;
		for(auto column : uniqueColumns){
			for(size_t row = 0; row < mData.size(); row++){
				res.mData[row].set(sid, column[row]);
			}
			sid++;
		}
		return res;
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
	
	size_t numSamples() const{
		size_t res = 0;
		for(auto& c : mData){
			res = std::max(res, c.size());
		}
		return res;
	}
	
	size_t numRemainingConstraints() const{
		size_t res = 0;
		for(auto& c : mData){
			if(c.any()) res++;
		}
		return res;
	}
	
	carl::Bitset getData(size_t id){
		return mData[id];
	}
	
	std::vector<std::pair<size_t, carl::Bitset>> getRemainingConstraints(){
		carl::Bitset mask(0);
		std::vector<size_t> ids;
		for (size_t id = 0; id < mData.size(); id++) {
			if (mData[id].any()){
				ids.push_back(id);
				mask |= mData[id];
			}
		}
		std::vector<std::pair<size_t, carl::Bitset>> res;
		for(auto id : ids){
			assert(mData[id].size() == mask.size());
			res.push_back(std::pair<size_t, carl::Bitset>(id, mData[id] | ~mask));
		}
		return res;
	}
	
	friend std::ostream& operator<<(std::ostream& os, const ConflictGraph& cg) {
		os << "Print CG with " << cg.mData.size() << " constraints" << std::endl;
		size_t numSamples = 0;
		for (auto c : cg.mData){
			numSamples = std::max(numSamples, c.size());
		}
		for (std::size_t i = 0; i < cg.mData.size(); i++) {
			if(cg.mData[i].any()){
				os << i << "\t" << 
					  std::string(numSamples-cg.mData[i].size(), '0') << cg.mData[i] <<
					  " : " << cg.mData[i].count() << std::endl;
			}
		}
		return os;
	}
};

}
}
