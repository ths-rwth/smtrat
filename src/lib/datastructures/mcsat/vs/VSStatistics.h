#pragma once

#include "../../../utilities/stats/Statistics.h"

#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat {
namespace mcsat {

class VSStatistics: public Statistics {
private:
	std::size_t mExplanationCalled = 0;
	std::size_t mExplanationSuccess = 0;
public:
	VSStatistics(const std::string& name): Statistics(name, this) {}
	~VSStatistics() = default;
	
	void collect() {
		Statistics::addKeyValuePair("explanation_called", mExplanationCalled);
		Statistics::addKeyValuePair("explanation_success", mExplanationSuccess);
	}
	
	void explanationCalled() {
		++mExplanationCalled;
	}

	void explanationSuccess() {
		++mExplanationSuccess;
	}
	
};

}
}

#endif
