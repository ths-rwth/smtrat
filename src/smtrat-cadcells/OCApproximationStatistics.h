#pragma once

#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat {
namespace cadcells {

class OCApproximationStatistics : public Statistics {
private:
	std::size_t mOneCellSuccess = 0; // #successfull calls
	std::size_t mApproximationConsidered = 0; // #calls using the approximation heuristic
	std::size_t mApproximated = 0; // #calls in which the approximation changed the cell
	std::size_t mApproximatedCellSuccess = 0; // #successful calls in which the approximation changed the cell
	std::size_t mArtificialPolys = 0; // #Polys introduced by the approximation

	bool mCurrentlyApproximated = false;
	std::map<std::size_t,std::size_t> mReplacedDegrees;

public:
	bool enabled() const {
		return true;
	}

	void collect() {
		Statistics::addKeyValuePair("onecell_success", mOneCellSuccess);
		Statistics::addKeyValuePair("approximated_cell_success", mApproximatedCellSuccess);
		Statistics::addKeyValuePair("approximation_considered", mApproximationConsidered);
		Statistics::addKeyValuePair("approximated", mApproximated);
		Statistics::addKeyValuePair("artificial_polys", mArtificialPolys);

		std::size_t maxDegree = 0; // mReplacedDegrees.rbegin(), relying on the order
		double degSum = 0.0;
		double nDegs = 0.0;
		for (const auto& [key, value] : mReplacedDegrees) {
			degSum += key*value;
			nDegs += value;
			if (key > maxDegree) maxDegree = key;
		}
		Statistics::addKeyValuePair("max_degree_replaced", maxDegree);
		Statistics::addKeyValuePair("mean_degree_replaced", (degSum/nDegs));
	}

	void success() {
		++mOneCellSuccess;
		if (mCurrentlyApproximated) {
			++mApproximatedCellSuccess;
			mCurrentlyApproximated = false;
		}
	}
	void approximationConsidered() {++mApproximationConsidered;}
	void artificialPoly() {
		++mArtificialPolys;
		if (!mCurrentlyApproximated) {
			++mApproximated;
			 mCurrentlyApproximated = true;
		}
	}
	void degreeReplaced(std::size_t d) {++mReplacedDegrees[d]; artificialPoly();}
};

OCApproximationStatistics& approximation_statistics() {
	static OCApproximationStatistics& statistics = statistics_get<OCApproximationStatistics>("mcsat-approximation-onecell");
	return statistics;
}

}
}

#endif
