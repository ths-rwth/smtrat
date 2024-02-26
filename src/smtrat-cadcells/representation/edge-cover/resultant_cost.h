#pragma once

#include "../../datastructures/projections.h"
#include "ordering_statistics.h"

namespace smtrat::cadcells::representation {

enum ResultantCostMethod {
	TOTAL_DEGREE_APPROXIMATE,
	TOTAL_DEGREE_EXACT,
	TOTAL_DEGREE_UPPER_BOUND
};

static const char* ResultantCostMethodStrings[] = {"TOTAL_DEGREE_APPROXIMATE",
												   "TOTAL_DEGREE_EXACT",
												   "TOTAL_DEGREE_UPPER_BOUND"};

template<ResultantCostMethod>
int compute(datastructures::Projections& proj, const datastructures::PolyRef& p1, const datastructures::PolyRef& p2);

template<>
inline int compute<ResultantCostMethod::TOTAL_DEGREE_APPROXIMATE>(datastructures::Projections& proj, const datastructures::PolyRef& p1, const datastructures::PolyRef& p2) {
	// TODO: Implement approximate total degree computation
	return 0;
}

template<>
inline int compute<ResultantCostMethod::TOTAL_DEGREE_EXACT>(datastructures::Projections& proj, const datastructures::PolyRef& p1, const datastructures::PolyRef& p2) {
	return proj.total_degree(proj.res(p1, p2));
}

template<>
inline int compute<ResultantCostMethod::TOTAL_DEGREE_UPPER_BOUND>(datastructures::Projections& proj, const datastructures::PolyRef& p1, const datastructures::PolyRef& p2) {
	return proj.total_degree(p1) * proj.total_degree(p2);
}

template<ResultantCostMethod M>
int calculate_cost(datastructures::Projections& proj, const datastructures::PolyRef& p1, const datastructures::PolyRef& p2) {
	SMTRAT_TIME_START(start);
	const auto cost = compute<M>(proj, p1, p2);
	SMTRAT_TIME_FINISH(optimal_edge_cover_stats.resultant_timer, start);
	SMTRAT_LOG_DEBUG("smtrat.cadcells.representation", "Cost of " << p1 << " and " << p2 << " is " << cost << " using " << M);
	SMTRAT_STATISTICS_CALL(optimal_edge_cover_stats.resultant_costs.add(cost));
	return cost;
}

inline std::ostream& operator<<(std::ostream& os, ResultantCostMethod method) {
	return os << ResultantCostMethodStrings[method];
}

} // namespace smtrat::cadcells::representation
