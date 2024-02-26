#pragma once

#include "edge_cover.h"
#include "resultant_cost.h"

namespace smtrat::cadcells::representation {

template<ResultantCostMethod M>
inline void optimal_edge_cover_ordering(datastructures::Projections& proj,
										const datastructures::Delineation& delin,
										const datastructures::DelineationInterval& delin_interval,
										const datastructures::SymbolicInterval& interval,
										datastructures::IndexedRootOrdering& ordering,
										boost::container::flat_set<datastructures::PolyRef>& equational,
										bool enable_weak,
										bool use_global_cache) {

	const auto& roots = delin.roots();

	if (roots.empty()) {
		SMTRAT_LOG_DEBUG("smtrat.cadcells.representation", "No roots in delin");
		return;
	}

	if (!delin_interval.upper_unbounded()) {
		SMTRAT_LOG_DEBUG("smtrat.cadcells.representation", "delin_interval.upper(): ");
		for (auto it = roots.end() - 1; it >= delin_interval.upper(); --it) {
			SMTRAT_LOG_DEBUG("smtrat.cadcells.representation", "Layer");
			for (const auto& t_root : it->second) {
				SMTRAT_LOG_DEBUG("smtrat.cadcells.representation", "\t" << t_root);
			}
		}
	}
	if (!delin_interval.lower_unbounded()) {
		SMTRAT_LOG_DEBUG("smtrat.cadcells.representation", "delin_interval.lower(): ");
		for (auto it = delin_interval.lower(); it >= roots.begin(); --it) {
			SMTRAT_LOG_DEBUG("smtrat.cadcells.representation", "Layer");
			for (const auto& t_root : it->second) {
				SMTRAT_LOG_DEBUG("smtrat.cadcells.representation", "\t" << t_root);
			}
		}
	}

	// create maps that maps each resultant to the roots it protects
	boost::container::flat_map<std::pair<datastructures::PolyRef, datastructures::PolyRef>,
							   std::pair<datastructures::IndexedRoot, datastructures::IndexedRoot>>
		cov_below, cov_above;

	// assign costs to resultants
	boost::container::flat_map<std::pair<datastructures::PolyRef, datastructures::PolyRef>, int> costs;

	// count how many vertices we will need in the graph later and assign indices to the roots
	std::map<datastructures::IndexedRoot, size_t> root_to_index;
	size_t n = 2;

	if (!delin_interval.lower_unbounded()) {
		const auto& lower = delin_interval.lower();

		// hack
		{
			const auto& t_root = lower->second.at(0);
			for (auto it = lower->second.begin() + 1; it != lower->second.end(); ++it) {
				ordering.add_less(t_root.root, it->root);
			}
		}

		for (auto it = lower; it != roots.begin(); --it) {
			for (const auto& t_root : it->second) {
				const auto& r1 = t_root.root;
				for (auto it2 = it - 1; it2 >= roots.begin(); --it2) {
					for (const auto& t_root2 : it2->second) {
						const auto& r2 = t_root2.root;

						const auto resultant = std::minmax(r1.poly, r2.poly);
						cov_below[resultant] = std::make_pair(r2, r1);

						// make sure we only assign one index to each root
						if (!root_to_index.contains(r2)) {
							root_to_index[r2] = n++;
						}

						costs[resultant] = calculate_cost<M>(proj, r1.poly, r2.poly);
					}
				}
			}
		}
	}

	if (!delin_interval.upper_unbounded()) {
		const auto upper = delin_interval.upper();

		// hack
		{
			const auto& t_root = upper->second.at(0);
			for (auto it = upper->second.begin() + 1; it != upper->second.end(); ++it) {
				ordering.add_less(it->root, t_root.root);
			}
		}

		for (auto it = upper; it != roots.end() - 1; ++it) {
			for (const auto& t_root : it->second) {
				const auto& r1 = t_root.root;
				for (auto it2 = it + 1; it2 != roots.end(); ++it2) {
					for (const auto& t_root2 : it2->second) {
						const auto& r2 = t_root2.root;

						const auto resultant = std::minmax(r1.poly, r2.poly);
						cov_above[resultant] = std::make_pair(r1, r2);

						// make sure we only assign one index to each root
						if (!root_to_index.contains(r2)) {
							root_to_index[r2] = n++;
						}

						// check if we already calculated the cost
						if (!costs.contains(resultant)) {
							costs[resultant] = calculate_cost<M>(proj, r1.poly, r2.poly);
						}
					}
				}
			}
		}
	}

	// create graph and create edge between dummy vertices
	util::Graph g(n);
	boost::add_edge(0, 1, 0, g);

	// remember which edge corresponds to which resultant
	std::map<util::Graph::edge_descriptor,
			 std::pair<datastructures::PolyRef, datastructures::PolyRef>>
		edge_to_resultant;

	int edge_index = 1;
	for (const auto& [resultant, cost] : costs) {
		int u = 0, v = 0;
		if (cov_below.contains(resultant)) {
			const auto [r1, r2] = cov_below[resultant];
			u = root_to_index[r1];
		}
		if (cov_above.contains(resultant)) {
			const auto [r1, r2] = cov_above[resultant];
			v = root_to_index[r2];
		}

		// add edge if it does not exist
		auto [edge, exists] = boost::edge(u, v, g);
		if (!exists) {
			edge = boost::add_edge(u, v, edge_index++, g).first;
		}

		// update edge weight if cost is lower
		const auto current_edge_weight = boost::get(boost::edge_weight, g, edge);
		if (current_edge_weight == 0 || cost < current_edge_weight) {
			boost::put(boost::edge_weight, g, edge, cost);
			edge_to_resultant[edge] = resultant;
		}
	}

	// solve minimum weight edge cover problem
	const auto [edge_cover, cost] = util::calculate_minimum_weight_edge_cover(g);

	// iterate over edges in edge cover and add the corresponding roots to the ordering
	for (const auto& edge : edge_cover) {
		const auto resultant = edge_to_resultant[edge];
		if (cov_below.contains(resultant)) {
			const auto [r1, r2] = cov_below[resultant];
			ordering.add_less(r1, r2);
		}
		if (cov_above.contains(resultant)) {
			const auto [r1, r2] = cov_above[resultant];
			ordering.add_less(r2, r1);
		}
	}

	SMTRAT_LOG_DEBUG("smtrat.cadcells.representation", "Optimal edge cover ordering: " << ordering);
	SMTRAT_LOG_DEBUG("smtrat.cadcells.representation", "Optimal edge cover cost: " << cost);
}

} // namespace smtrat::cadcells::representation
