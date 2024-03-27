#pragma once

#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat {
namespace mcsat {

class NLSATStatistics: public Statistics {
private:
	std::size_t mExplanationCalled = 0;
	std::size_t mExplanationSuccess = 0;
	carl::statistics::Timer mTimer;
public:
	bool enabled() const {
		return (mExplanationCalled > 0) || (mExplanationSuccess > 0);
	}
	void collect() {
		Statistics::addKeyValuePair("explanation_called", mExplanationCalled);
		Statistics::addKeyValuePair("explanation_success", mExplanationSuccess);
		Statistics::addKeyValuePair("timer", mTimer);
	}
	
	void explanationCalled() {
		++mExplanationCalled;
	}

	void explanationSuccess() {
		++mExplanationSuccess;
	}

	void timer_start() {
        mTimer.start_this();
    }
	void timer_finish() {
        mTimer.finish();
    }
	
};

}
}

#endif
