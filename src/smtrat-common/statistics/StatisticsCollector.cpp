#include "StatisticsCollector.h"

#include "Statistics.h"

namespace smtrat {

void StatisticsCollector::collect() {
	for (auto s: mStats) s->collect();
}

}