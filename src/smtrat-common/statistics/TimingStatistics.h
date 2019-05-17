#pragma once

#include "Statistics.h"

#ifdef SMTRAT_DEVOPTION_Statistics

#include <carl/util/TimingCollector.h>

namespace smtrat {

class TimingStatistics: public Statistics {
private:

public:
	bool enabled() const {
		return true;
	}
    void addTimingCollector(const carl::TimingCollector& tc) {
        for (const auto& d: tc.data()) {
            Statistics::addKeyValuePair(d.first + " (duration in ms)", d.second.overall.count());
            Statistics::addKeyValuePair(d.first + " (count)", d.second.count);
        }
    }
	void collect() {
	}
	
};

}

#endif
