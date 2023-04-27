/**
 * @file NewCoveringStatistics.h
 * @author Philip Kroll <Philip.Kroll@rwth-aachen.de>
 *
 * @version 21.01.2022
 * Created on 21.01.2022
 */

#pragma once

#include <chrono>
#include <string>
#include <map>
#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat {
class NewCoveringStatistics : public Statistics {
private:
	bool didHeuristicUseTheorem = false;

	std::size_t mTotalCalls = 0;
	std::size_t mIncrementalOnlyCalls = 0;
	std::size_t mBacktrackingOnlyCalls = 0;
	std::size_t mIncrementalAndBacktrackingCalls = 0;
	std::size_t mDimension = 0;
	std::size_t mIntervals = 0;
	std::size_t mClosedIntervals = 0;
	std::string mVariableOrderingType = "";
	std::string mCoveringHeuristicType = "";
	std::string mOperatorType = "";
	std::string mSamplingAlgorithm = "";
	std::string mIsSampleOutsideAlgorithm = "";
	std::size_t mTotalSamples = 0;
	std::size_t mBoundSamples = 0;
	std::size_t mTotalPartialSamples = 0;
	std::size_t mRanPartialSamples = 0;
	std::size_t mTotalSamplesInGetUnsat = 0;
	std::size_t mRanSamplesInGetUnsat = 0;
	std::map<size_t, std::map<size_t, size_t>> mHeuristicCall; // Map[Level interval][Max level constraints] --> # heuristic calls
	std::map<size_t, std::map<size_t, size_t>> mTheoremHolds;
	std::map<size_t, size_t> heuristicUsedTheorem;
	std::map<size_t, size_t> heuristicUsed;
	std::size_t mHeuristicUsesTheorem = 0;
	std::size_t mLevelTheorem = 0;
	carl::statistics::timer mTimerComputeCovering;
	carl::statistics::timer mTimerConstructDerivation;

	std::vector<carl::Variable> mVariableOrdering;

public:

	void setVariableOrdering(std::vector<carl::Variable>& varOrdering) {
		mVariableOrdering = varOrdering;
	}

	std::vector<carl::Variable> getVariableOrdering() {
		return mVariableOrdering;
	}
       
	std::string map_to_string(std::map<size_t,size_t>  &m) {
		std::string output = "";
		std::string value = "";
		std::string result = "";

		for (auto it = m.cbegin(); it != m.cend(); it++) {
			value = std::to_string(it->second);
			output += std::to_string(it->first) + "," + (value) + ";";
		}

		result = output.substr(0, output.size() - 1 );

		return result;
	}

	std::string map_to_string(std::map<size_t, std::map<size_t, size_t>>  &m) {
		std::string output = "";
		std::string value = "";
		std::string result = "";

		for (auto itr = m.begin(); itr != m.end(); itr++) {
			for (auto ptr = itr->second.begin(); ptr != itr->second.end(); ptr++) {
				output += "" + std::to_string(itr->first) + "," + 
					std::to_string(ptr->first) + "," +
					std::to_string(ptr->second) + ";";
			}
		}

		result = output.substr(0, output.size() - 1);

		return result;
	}

	std::string map_to_string(std::map<size_t,std::string>  &m) {
		std::string output = "";
		std::string value = "";
		std::string result = "";

		for (auto it = m.cbegin(); it != m.cend(); it++) {
			value = it->second;
			output += std::to_string(it->first) + ";" + (value) + ", ";
		}

		result = output.substr(0, output.size() - 2 );

		return result;
	}

	void collect() {
		Statistics::addKeyValuePair("total_calls", mTotalCalls);
		Statistics::addKeyValuePair("incremental_only_calls", mIncrementalOnlyCalls);
		Statistics::addKeyValuePair("backtracking_only_calls", mBacktrackingOnlyCalls);
		Statistics::addKeyValuePair("incremental_and_backtracking_calls", mIncrementalAndBacktrackingCalls);
		Statistics::addKeyValuePair("dimension", mDimension);
		Statistics::addKeyValuePair("time_compute_covering", mTimerComputeCovering);
		Statistics::addKeyValuePair("time_construct_derivation", mTimerConstructDerivation);
		Statistics::addKeyValuePair("variable_ordering_type", mVariableOrderingType);
		Statistics::addKeyValuePair("covering_heuristic_type", mCoveringHeuristicType);
		Statistics::addKeyValuePair("operator_type", mOperatorType);
		Statistics::addKeyValuePair("sampling_algorithm", mSamplingAlgorithm);
		Statistics::addKeyValuePair("is_sample_outside_algorithm", mIsSampleOutsideAlgorithm);
		Statistics::addKeyValuePair("total_samples", mTotalSamples);
		Statistics::addKeyValuePair("intervals", mIntervals);
		Statistics::addKeyValuePair("closed_intervals", mClosedIntervals);
		Statistics::addKeyValuePair("bound_samples", mBoundSamples);
		Statistics::addKeyValuePair("partial_total_samples", mTotalPartialSamples); // Number of samples used in the algorithm
		Statistics::addKeyValuePair("partial_ran_samples", mRanPartialSamples); // Number of samples with at least one non-rational component used in the algorithm
        Statistics::addKeyValuePair("heuristic_called", map_to_string(mHeuristicCall)); // All inferred intervals
        Statistics::addKeyValuePair("theorem_holds", map_to_string(mTheoremHolds)); // All inferred intervals with theorem
	}

	void calledSample() {
		mTotalSamples++;
	}
	void calledBoundSample() {
		calledSample();
		mBoundSamples++;
	}
	void calledBoundSample(bool non_rational) {
		calledSample();
		mBoundSamples += non_rational;
	}
	void calledSampleExtend(carl::ran_assignment<Rational>& currentAssignment, size_t currentLevel, bool newComponentNonRational) {
		mTotalPartialSamples += 1;
		if(newComponentNonRational) {
			mRanPartialSamples += 1;
		} else {
			bool foundRan = false;
			for(size_t i = 0; i < currentLevel; i++) {
				foundRan = foundRan || !currentAssignment[mVariableOrdering[i]].is_numeric();
				if(foundRan) {
					break;
				}
			}
			mRanPartialSamples += foundRan;
		}
	}

	void getUnsatSampleSample(carl::ran_assignment<Rational>& currentAssignment, size_t currentLevel) {
		bool foundRan = false;
		for(size_t i = 0; i < currentLevel; i++) {
			foundRan = foundRan || !currentAssignment[mVariableOrdering[i]].is_numeric();
			if(foundRan) {
				break;
			}
		}
		mTotalSamplesInGetUnsat++;
		mRanSamplesInGetUnsat += foundRan;
	}

	void heuristicUse(bool withTheorem) {
		didHeuristicUseTheorem = withTheorem;
		mHeuristicUsesTheorem += withTheorem;
	}

	void storeHeuristicUsed(size_t level) {
		if(didHeuristicUseTheorem) {
			heuristicUsedTheorem[mVariableOrdering.size() - level - 1] += 1;
		}
		heuristicUsed[mVariableOrdering.size() - level - 1] += 1;
		didHeuristicUseTheorem = false;
	}

	void called() {
		mTotalCalls++;
	}

	void calledIncrementalOnly() {
		mIncrementalOnlyCalls++;
	}
	void calledBacktrackingOnly() {
		mBacktrackingOnlyCalls++;
	}
	void calledIncrementalAndBacktracking() {
		mIncrementalAndBacktrackingCalls++;
	}

	void setDimension(std::size_t dimension) {
		mDimension = dimension;
	}

	auto& timeForComputeCovering() {
		return mTimerComputeCovering;
	}

	auto& timeForConstructDerivation() {
		return mTimerConstructDerivation;
	}

	void setVariableOrderingType(std::string variableOrderingType) {
		mVariableOrderingType = variableOrderingType;
	}

	void setCoveringHeuristicType(std::string coveringHeuristicType) {
		mCoveringHeuristicType = coveringHeuristicType;
	}

	void setOperatorType(std::string operatorType) {
		mOperatorType = operatorType;
	}

	void setSamplingAlgorithm(std::string samplingAlgorithm) {
		mSamplingAlgorithm = samplingAlgorithm;
	}

	void setIsSampleOutsideAlgorithm(std::string isSampleOutsideAlgorithm) {
		mIsSampleOutsideAlgorithm = isSampleOutsideAlgorithm;
	}

	void derivedInterval(bool isClosed) {
		mClosedIntervals += isClosed;
	}

	void derivedInterval() {
		mIntervals++;
	}

	void levelWiseCreatedInterval(bool theoremHolds, size_t level, size_t max_level) {
		mHeuristicCall[level][max_level] += 1;
		if(theoremHolds) {
			mTheoremHolds[level][max_level] += 1;
		}
		mLevelTheorem += theoremHolds;
	}

};

static auto& getStatistics() {
	SMTRAT_STATISTICS_INIT_STATIC(NewCoveringStatistics, stats, "NewCoveringModule");
	return stats;
}

} // namespace smtrat

#endif
