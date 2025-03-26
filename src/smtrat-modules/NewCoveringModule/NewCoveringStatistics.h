/**
 * @file NewCoveringStatistics.h
 * @author Philip Kroll <Philip.Kroll@rwth-aachen.de>
 *
 * @version 21.01.2022
 * Created on 21.01.2022
 */

#pragma once

#include <chrono>
#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat {
class NewCoveringStatistics : public Statistics {
private:
    std::size_t mTotalCalls = 0;
    bool isIncremental = false;
    bool isBacktracking = false;
    std::size_t mIncrementalOnlyCalls = 0;
    std::size_t mBacktrackingOnlyCalls = 0;
    std::size_t mIncrementalAndBacktrackingCalls = 0;
    std::size_t mDimension = 0;
    std::string mVariableOrderingType = "";
    std::string mCoveringHeuristicType = "";
    std::string mOperatorType = "";
    std::string mSamplingAlgorithm = "";
    std::string mIsSampleOutsideAlgorithm = "";
    carl::statistics::Timer mTimerComputeCovering;
    carl::statistics::Timer mTimerConstructDerivation;
    std::size_t m_num_characterize_covering = 0;

public:
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
        Statistics::addKeyValuePair("is_incremental", isIncremental);
        Statistics::addKeyValuePair("is_backtracking", isBacktracking);
        Statistics::addKeyValuePair("characterize_covering.count", m_num_characterize_covering);
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

    void setVariableOrderingType(const std::string& variableOrderingType) {
        mVariableOrderingType = variableOrderingType;
    }

    void setCoveringHeuristicType(const std::string& coveringHeuristicType) {
        mCoveringHeuristicType = coveringHeuristicType;
    }

    void setOperatorType(const std::string& operatorType) {
        mOperatorType = operatorType;
    }

    void setSamplingAlgorithm(const std::string& samplingAlgorithm) {
        mSamplingAlgorithm = samplingAlgorithm;
    }

    void setIsSampleOutsideAlgorithm(const std::string& isSampleOutsideAlgorithm) {
        mIsSampleOutsideAlgorithm = isSampleOutsideAlgorithm;
    }

    void setIncremental(bool incremental) {
        isIncremental = incremental;
    }

    void setBacktracking(bool backtracking) {
        isBacktracking = backtracking;
    }

    void characterize_covering() {
        m_num_characterize_covering++;
    }
};

static auto& getStatistics() {
    SMTRAT_STATISTICS_INIT_STATIC(NewCoveringStatistics, stats, "NewCoveringModule");
    return stats;
}

} // namespace smtrat

#endif
