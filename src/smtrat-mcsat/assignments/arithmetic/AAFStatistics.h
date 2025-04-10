#pragma once

#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat {
namespace mcsat {

class AAFStatistics: public Statistics {
private:
	std::size_t mCalled = 0;
	std::size_t mSuccess = 0;

public:
	carl::statistics::Timer m_timer_evaluate;
	carl::statistics::Timer m_timer_real_root_isolation;
public:
	bool enabled() const {
		return (mCalled > 0) || (mSuccess > 0);
	}
	void collect() {
		Statistics::addKeyValuePair("called", mCalled);
		Statistics::addKeyValuePair("success", mSuccess);
		Statistics::addKeyValuePair("timer.evaluate", m_timer_evaluate);
		Statistics::addKeyValuePair("timer.real_root_isolation", m_timer_real_root_isolation);
	}
	
	void called() {
		++mCalled;
	}

	void success() {
		++mSuccess;
	}
	
};

}
}

#endif
