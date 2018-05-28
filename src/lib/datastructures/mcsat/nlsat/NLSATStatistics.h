#pragma once

#include "../../../utilities/stats/Statistics.h"

#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat {
namespace mcsat {

class NLSATStatistics: public Statistics {
private:
	std::size_t mNrExplanations = 0;
public:
	NLSATStatistics(const std::string& name): Statistics(name, this) {}
	~NLSATStatistics() = default;
	
	void collect() {
		Statistics::addKeyValuePair("explanations", mNrExplanations);
	}
	
	void explanation() {
		++mNrExplanations;
	}
	
};

}
}

#endif
