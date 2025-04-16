#pragma once

#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat::cadcells::representation::combinatorialopt {
class OrderingStatistics : public Statistics {
public:
	carl::statistics::Series ordering_costs;
	carl::statistics::Timer ordering_timer;
	carl::statistics::Series resultant_costs;
	carl::statistics::Timer resultant_timer;
	std::size_t hack_applied = 0;

	void collect() {
		Statistics::addKeyValuePair("ordering_costs", ordering_costs);
		Statistics::addKeyValuePair("ordering_timer", ordering_timer);
		Statistics::addKeyValuePair("resultant_costs", resultant_costs);
		Statistics::addKeyValuePair("resultant_timer", resultant_timer);
		Statistics::addKeyValuePair("hack_applied", hack_applied);
	}
};

OrderingStatistics& ordering_statistics();


} // namespace smtrat::cadcells::representation

#endif
