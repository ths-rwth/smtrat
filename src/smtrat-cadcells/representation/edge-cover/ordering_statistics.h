#pragma once

#include "resultant_cost.h"

#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat::cadcells::representation {
class OptimalEdgeCoverStatistics : public Statistics {
private:
public:
	carl::statistics::Series ordering_costs;
	carl::statistics::Timer ordering_timer;
	carl::statistics::Series resultant_costs;
	carl::statistics::Timer resultant_timer;
	int counter = 0;

	void collect() {
		Statistics::addKeyValuePair("ordering_costs", ordering_costs);
		Statistics::addKeyValuePair("ordering_timer", ordering_timer);
		Statistics::addKeyValuePair("resultant_costs", resultant_costs);
		Statistics::addKeyValuePair("resultant_timer", resultant_timer);
		Statistics::addKeyValuePair("counter", counter);
	}
};

SMTRAT_STATISTICS_INIT_STATIC(OptimalEdgeCoverStatistics, optimal_edge_cover_stats, "OptimalEdgeCover");

/*
template<ResultantCostMethod M>
inline void log_ordering_cost(datastructures::Projections& proj, const datastructures::IndexedRootOrdering& ordering) {
	auto cost = 0;
	std::set<std::pair<datastructures::PolyRef, datastructures::PolyRef>> resultants;
	for (const auto p : ordering.polys()) {
		for (const auto q : ordering.polys()) {
			const auto resultant = std::minmax(p, q);
			if (resultants.find(resultant) == resultants.end()) {
				cost += calculate_cost<M>(proj, p, q);
				resultants.insert(resultant);
			}
		}
	}
	SMTRAT_STATISTICS_CALL(optimal_edge_cover_stats.resultant_costs.add(cost));
}
*/

} // namespace smtrat::cadcells::representation

#endif
