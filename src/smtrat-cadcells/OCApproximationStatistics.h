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
	std::size_t mUnboundedLevels = 0;
	std::size_t mHalfUnboundedLevels = 0;
	std::size_t mResultants = 0;
	std::size_t mDiscriminants = 0;
	std::size_t mCoefficients = 0;

	bool mCurrentlyApproximated = false;
	std::map<std::size_t,std::size_t> mReplacedDegrees;
	std::map<std::size_t,std::size_t> mDegrees;

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
		Statistics::addKeyValuePair("unbounded_levels", mUnboundedLevels);
		Statistics::addKeyValuePair("half_unbounded_levels", mHalfUnboundedLevels);
		Statistics::addKeyValuePair("resultants", mResultants);
		Statistics::addKeyValuePair("discriminants", mDiscriminants);
		Statistics::addKeyValuePair("leading_coefficients", mCoefficients);

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

		maxDegree = 0; // mDegreesInConstruction.rbegin(), relying on the order
		degSum = 0.0, nDegs = 0.0;
		for (const auto& [key, value] : mDegrees) {
			degSum += key*value;
			nDegs += value;
			if (key > maxDegree) maxDegree = key;
		}
		Statistics::addKeyValuePair("max_degree_construction", maxDegree);
		Statistics::addKeyValuePair("mean_degree_construction", (degSum/nDegs));
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
	void degree(std::size_t d) {++mDegrees[d];}
	void unboundedLevel() {++mUnboundedLevels;}
	void halfUnboundedLevel() {++mHalfUnboundedLevels;}
	void resultant() {++mResultants;}
	void discriminant() {++mDiscriminants;}
	void coefficient() {++mCoefficients;}

	static OCApproximationStatistics& get_instance() {
		static OCApproximationStatistics& statistics = statistics_get<OCApproximationStatistics>("mcsat-approximation-onecell");
		return statistics;
	}
};

}
}

#endif
