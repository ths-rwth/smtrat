#pragma once

#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat {
namespace cadcells {

class OCApproximationStatistics : public Statistics {
private:
	using Counter = std::map<std::size_t, std::size_t>;

	bool mCurrentlyApproximated = false; // helper variable: is the current cell approximated?

	std::size_t mConsidered = 0; 			// #calls using the approximation heuristic
	std::size_t mApproximated = 0; 			// #calls actually approximating
	std::size_t mApproximatedSuccess = 0; 	// #successful calls actually approximating

	Counter mApproximatedDegrees;	// Counts approximations for each degree

	std::vector<std::pair<std::size_t,std::size_t>>  mTaylorIgnoredVars; // For each taylor-approximated polynomial, #variables left out and # variables
	std::size_t mTaylorFailure = 0; // #times the taylor method fails because of gradient 0

	std::size_t mUnboundedLevels = 0; 			// #unbounded levels in the constructed cells
	std::size_t mHalfUnboundedLevels = 0; 		// #one side unbounded levels in the constructed cells
	std::vector<std::size_t> mCellDimensions;	// Dimension of the constructed cells

	std::size_t mResultants = 0; 	// #computed resultants
	std::size_t mDiscriminants = 0; // #computed discriminants
	std::size_t mCoefficients = 0; 	// #computed leading coefficients
	Counter mDegrees; 				// Counts the occuring degrees of all constructed polynomials

	std::size_t mInvolvedTooOften = 0; 	// #times a constraint was involved in too many conflicts
	std::size_t mPolyApxTooOften = 0; 	// #times a poly was approximated too often
	bool mMaxConsideredReached = false; // flag whether the max number of apx considered is reached
	bool mMaxApxReached = false; 		// flag whether the max number of apx is reached

	void collectCounterStats(Counter c, const std::string& name) {
		std::size_t max = 0;
		std::size_t n = 0;
		std::size_t sum = 0;
		for (const auto& [key, value] : c) {
			n += value;
			sum += key * value;
			if (key > max) max = key;
		}
		double mean = ((double) sum) / ((double) n);
		Statistics::addKeyValuePair("total_"+name, n);
		Statistics::addKeyValuePair("max_"+name, max);
		Statistics::addKeyValuePair("mean_"+name, mean);
	}

public:
	bool enabled() const {
		return true;
	}

	void collect() {
		Statistics::addKeyValuePair("considered", mConsidered);
		Statistics::addKeyValuePair("approximated", mApproximated);
		Statistics::addKeyValuePair("success", mApproximatedSuccess);

		collectCounterStats(mApproximatedDegrees, "apx_degrees");

		Statistics::addKeyValuePair("unbounded_levels", mUnboundedLevels);
		Statistics::addKeyValuePair("half_unbounded_levels", mHalfUnboundedLevels);
		std::size_t sumDimensions = 0;
		for (const std::size_t d : mCellDimensions) sumDimensions += d;
		Statistics::addKeyValuePair("mean_cell_dimension", ((double) sumDimensions) / ((double) mCellDimensions.size()));

		std::size_t maxIgnoredVars = 0;
		double sum = 0.0;
		std::size_t total = 0;
		for (const auto& item : mTaylorIgnoredVars) {
			sum += ((double) item.first) / ((double) item.second);
			total += item.first;
			if (item.first > maxIgnoredVars) maxIgnoredVars = item.first;
		}
		double meanIgnoredVars = sum/((double) mTaylorIgnoredVars.size());
		Statistics::addKeyValuePair("max_taylor_ignored_vars", maxIgnoredVars);
		Statistics::addKeyValuePair("total_taylor_ignored_vars", total);
		Statistics::addKeyValuePair("mean_taylor_ignored_vars", meanIgnoredVars);
		Statistics::addKeyValuePair("taylor_failure", mTaylorFailure);

		Statistics::addKeyValuePair("resultants", mResultants);
		Statistics::addKeyValuePair("discriminants", mDiscriminants);
		Statistics::addKeyValuePair("leading_coefficients", mCoefficients);
		collectCounterStats(mDegrees, "construction_degrees");

		Statistics::addKeyValuePair("involved_to_often", mInvolvedTooOften);
		Statistics::addKeyValuePair("apx_to_often", mPolyApxTooOften);
		Statistics::addKeyValuePair("max_considered_reached", mMaxConsideredReached);
		Statistics::addKeyValuePair("max_apx_reached", mMaxApxReached);
	}

	void newCell() {
		mCurrentlyApproximated = false;
	}

	void success(std::size_t d) {
		if (mCurrentlyApproximated) ++mApproximatedSuccess;
		mCellDimensions.push_back(d);
	}
	void approximationConsidered() {++mConsidered;}
	void approximated(std::size_t d) {
		++mApproximatedDegrees[d];
		if (!mCurrentlyApproximated) {
			++mApproximated;
			 mCurrentlyApproximated = true;
		}
	}

	void taylorIgnoredVars(std::size_t ignored, std::size_t total) {mTaylorIgnoredVars.emplace_back(ignored, total);}
	void taylorFailure() {++mTaylorFailure;}

	void unboundedLevel() {++mUnboundedLevels;}
	void halfUnboundedLevel() {++mHalfUnboundedLevels;}
	void cellDimension(std::size_t d) {mCellDimensions.push_back(d);}

	void resultant() {++mResultants;}
	void discriminant() {++mDiscriminants;}
	void coefficient() {++mCoefficients;}
	void degree(std::size_t d) {++mDegrees[d];}

	void involvedTooOften() {++mInvolvedTooOften;}
	void apxTooOften() {++mPolyApxTooOften;}
	void maxConsideredReached() {mMaxConsideredReached = true;}
	void maxApxReached() {mMaxApxReached = true;}

	static OCApproximationStatistics& get_instance() {
		static OCApproximationStatistics& statistics = statistics_get<OCApproximationStatistics>("onecell-approximation");
		return statistics;
	}
};

}
}

#endif