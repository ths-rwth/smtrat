#pragma once

#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat {
namespace cadcells {

class PolyPoolStatistics : public Statistics {
private:
	std::map<std::size_t,std::size_t> mDegrees;

public:
	bool enabled() const {
		return true;
	}

	void collect() {
		std::size_t maxDegree = 0; // mDegreesInConstruction.rbegin(), relying on the order
		double degSum = 0.0, nDegs = 0.0;
		for (const auto& [key, value] : mDegrees) {
			degSum += key*value;
			nDegs += value;
			if (key > maxDegree) maxDegree = key;
		}
		Statistics::addKeyValuePair("max_degree_construction", maxDegree);
		Statistics::addKeyValuePair("mean_degree_construction", (degSum/nDegs));
	}

	void degree(std::size_t d) {++mDegrees[d];}

	static PolyPoolStatistics& get_instance() { // TODO: replace by real singleton
		static PolyPoolStatistics& statistics = statistics_get<PolyPoolStatistics>("mcsat-polys-onecell");
		return statistics;
	}
};

}
}

#endif
