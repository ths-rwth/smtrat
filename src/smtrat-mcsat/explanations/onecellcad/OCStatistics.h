#pragma once

#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat {
namespace mcsat {
namespace onecellcad {

class OCStatistics : public Statistics {
private:
	std::size_t mExplanationCalled = 0;
	std::size_t mExplanationSuccess = 0;
	// counts the number of "resultant-barriers" created in the third (smart Heuristic)
	std::size_t mResultantBarriersH3 = 0;
	// saves the maximal degree a polynomial has during calculations
	std::size_t mMaxDegree = 0;

public:
	bool enabled() const {
		return true;
	}

	void collect() {
		Statistics::addKeyValuePair("explanation_called", mExplanationCalled);
		Statistics::addKeyValuePair("explanation_success", mExplanationSuccess);
        Statistics::addKeyValuePair("resultant_barriers", mResultantBarriersH3);
        Statistics::addKeyValuePair("max_degree", mMaxDegree);
	}

	void explanationCalled() {
		++mExplanationCalled;
	}

	void explanationSuccess() {
		++mExplanationSuccess;
	}

	void resultantBarrierCreated(){
	    ++mResultantBarriersH3;
	}

	// To disable this statistics, set variable in appendOnCorrectLevel() in utils.h
	void updateMaxDegree(std::size_t NewDeg){
	    mMaxDegree = NewDeg;
	}

	std::size_t getCurrentMaxDegree(){
	    return mMaxDegree;
	}
};

}
}
}

#endif
