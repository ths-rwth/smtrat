#pragma once

#include <algorithm>
#include <numeric>
#include <vector>

#include "../../datastructures/projections.h"
#include "ordering_statistics.h"

namespace smtrat::cadcells::representation {

enum ResultantCostMethod {
	FEATURE_BASED,
	VARIABLE_DEPTH,
	TOTAL_DEGREE_UPPER_BOUND,
	TOTAL_DEGREE_EXACT,
	SUM_OVER_TOTAL_DEGREE,
	NUM_VARIABLES,
	NUM_RESULTANTS,
	NUM_MONOMIALS,
	HIGHEST_MONOMIAL
};

static const char* ResultantCostMethodStrings[] = {
	"FEATURE_BASED",
	"VARIABLE_DEPTH",
	"TOTAL_DEGREE_UPPER_BOUND",
	"TOTAL_DEGREE_EXACT",
	"SUM_OVER_TOTAL_DEGREE",
	"NUM_VARIABLES",
	"NUM_RESULTANTS",
	"NUM_MONOMIALS",
	"HIGHEST_MONOMIAL"};

inline auto get_union_of_variables(datastructures::Projections& proj,
								   const datastructures::PolyRef p1,
								   const datastructures::PolyRef p2) {
	auto p1_vars = proj.variables(p1),
		 p2_vars = proj.variables(p2);

	std::sort(p1_vars.begin(), p1_vars.end());
	std::sort(p2_vars.begin(), p2_vars.end());

	std::vector<carl::Variable> res_vars(p1_vars.size() + p2_vars.size());
	auto it = std::set_union(p1_vars.begin(), p1_vars.end(),
							 p2_vars.begin(), p2_vars.end(),
							 res_vars.begin());
	res_vars.resize(it - res_vars.begin());
	return res_vars;
}

template<ResultantCostMethod>
int compute(datastructures::Projections& proj,
			const datastructures::PolyRef p1,
			const datastructures::PolyRef p2);

template<>
inline int compute<ResultantCostMethod::FEATURE_BASED>(datastructures::Projections& proj,
													   const datastructures::PolyRef p1,
													   const datastructures::PolyRef p2) {
	const auto& polys = proj.polys();
	const auto poly1 = polys(p1),
			   poly2 = polys(p2);
	const auto degree_p1 = poly1.degree(),
			   degree_p2 = poly2.degree();
	return degree_p1 + degree_p2;
}

inline auto base_level(const auto& vars, const auto& var_order) {
	datastructures::level_t lvl = 0;
	for (datastructures::level_t i = 0; i < var_order.size(); ++i) {
		if (std::find(vars.begin(), vars.end(), var_order[i]) != vars.end()) lvl = i + 1;
	}
	return lvl;
}

template<>
inline int compute<ResultantCostMethod::VARIABLE_DEPTH>(datastructures::Projections& proj,
														const datastructures::PolyRef p1,
														const datastructures::PolyRef p2) {
	const auto& polys = proj.polys();
	const auto main_var = polys(p1).main_var();

	auto res_vars = get_union_of_variables(proj, p1, p2);
	res_vars.erase(std::remove(res_vars.begin(), res_vars.end(), main_var), res_vars.end());

	return base_level(res_vars, polys.var_order());
}

template<>
inline int compute<ResultantCostMethod::TOTAL_DEGREE_UPPER_BOUND>(datastructures::Projections& proj,
																  const datastructures::PolyRef p1,
																  const datastructures::PolyRef p2) {
	return proj.total_degree(p1) * proj.total_degree(p2);
}

template<>
inline int compute<ResultantCostMethod::TOTAL_DEGREE_EXACT>(datastructures::Projections& proj,
															const datastructures::PolyRef p1,
															const datastructures::PolyRef p2) {
	auto& polys = proj.polys();
	const auto result = polys(carl::resultant(polys(p1), polys(p2)));
	return proj.total_degree(result);
}

template<>
inline int compute<ResultantCostMethod::SUM_OVER_TOTAL_DEGREE>(datastructures::Projections& proj,
															   const datastructures::PolyRef p1,
															   const datastructures::PolyRef p2) {
	const auto monomial_total_degrees_p1 = proj.monomial_total_degrees(p1),
			   monomial_total_degrees_p2 = proj.monomial_total_degrees(p2);
	return std::accumulate(monomial_total_degrees_p1.begin(), monomial_total_degrees_p1.end(), 0) +
		   std::accumulate(monomial_total_degrees_p2.begin(), monomial_total_degrees_p2.end(), 0);
}

template<>
inline int compute<ResultantCostMethod::NUM_VARIABLES>(datastructures::Projections& proj,
													   const datastructures::PolyRef p1,
													   const datastructures::PolyRef p2) {
	const auto res_vars = get_union_of_variables(proj, p1, p2);
	return res_vars.size() - 1;
}

template<>
inline int compute<ResultantCostMethod::NUM_RESULTANTS>(datastructures::Projections& proj,
														const datastructures::PolyRef p1,
														const datastructures::PolyRef p2) {
	return 1;
}

template<>
inline int compute<ResultantCostMethod::NUM_MONOMIALS>(datastructures::Projections& proj,
													   const datastructures::PolyRef p1,
													   const datastructures::PolyRef p2) {
	const auto monomial_total_degrees_p1 = proj.monomial_total_degrees(p1),
			   monomial_total_degrees_p2 = proj.monomial_total_degrees(p2);
	const auto p1_num_monomials = monomial_total_degrees_p1.size(),
			   p2_num_monomials = monomial_total_degrees_p2.size();
	return p1_num_monomials + p2_num_monomials;
}

template<>
inline int compute<ResultantCostMethod::HIGHEST_MONOMIAL>(datastructures::Projections& proj,
														  const datastructures::PolyRef p1,
														  const datastructures::PolyRef p2) {
	// TODO: Implement this
	return 0;
}

template<ResultantCostMethod M>
int calculate_cost(datastructures::Projections& proj,
				   const datastructures::PolyRef p1,
				   const datastructures::PolyRef p2) {
	SMTRAT_TIME_START(start);
	const auto cost = compute<M>(proj, p1, p2);
	SMTRAT_TIME_FINISH(ordering_stats.resultant_timer, start);
	SMTRAT_LOG_DEBUG("smtrat.cadcells.representation", "Cost of " << p1 << " and " << p2 << " is " << cost << " using " << M);
	SMTRAT_STATISTICS_CALL(ordering_stats.resultant_costs.add(cost));
	return cost;
}

inline std::ostream& operator<<(std::ostream& os, ResultantCostMethod method) {
	return os << ResultantCostMethodStrings[method];
}

} // namespace smtrat::cadcells::representation
