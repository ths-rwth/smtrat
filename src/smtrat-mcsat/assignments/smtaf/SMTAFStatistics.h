#pragma once

#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat {
namespace mcsat {

class SMTAFStatistics: public Statistics {
private:
	std::size_t mCalled = 0;
	std::size_t mSuccess = 0;
public:
	bool enabled() const {
		return (mCalled > 0) || (mSuccess > 0);
	}
	void collect() {
		Statistics::addKeyValuePair("called", mCalled);
		Statistics::addKeyValuePair("success", mSuccess);
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
