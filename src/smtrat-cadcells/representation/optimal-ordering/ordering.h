#pragma once

#include <map>
#include <string>
#include <vector>

#include <boost/algorithm/string/join.hpp>
#include <boost/range/adaptor/transformed.hpp>
#include <boost/stl_interfaces/reverse_iterator.hpp>

#include "../../datastructures/roots.h"
#include "graph.h"
#include "matching.h"
#include "ordering_statistics.h"
#include "resultant_cost_metrics.h"

namespace smtrat::cadcells::representation {

typedef std::pair<datastructures::PolyRef, datastructures::PolyRef> PolyPair;

template<ResultantCostMethod M>
inline auto get_candidate_resultants(auto& proj, const auto& delin,
									 const auto& delin_interval, auto& ordering) {
	// create maps that maps each resultant to the roots it protects
	std::map<PolyPair, util::RootPair> cov_below, cov_above, layer_below, layer_above;

	// assign costs to resultants
	std::map<PolyPair, int> costs;

	// count how many vertices we will need in the graph later and assign indices to the roots
	std::map<datastructures::IndexedRoot, size_t> root_to_index;
	size_t n = 2;

	auto test = [&](auto& cov, auto& layer, const auto begin, const auto end) {
		bool closest = true;
		for (auto it = begin; it != end; ++it) {
			for (auto it1_layer = it->second.begin(); it1_layer != it->second.end(); ++it1_layer) {
				const auto& r1 = it1_layer->root;
				if (!closest) {
					for (auto it2_layer = it1_layer + 1; it2_layer < it->second.end(); ++it2_layer) {
						const auto& r2 = it2_layer->root;

						const auto resultant = std::minmax(r1.poly, r2.poly);
						layer.emplace(resultant, std::make_pair(r1, r2));

						// make sure we only assign one index to each root
						if (!root_to_index.contains(r2)) {
							root_to_index.emplace(r2, n++);
						}

						// check if we already calculated the cost
						if (!costs.contains(resultant)) {
							costs.emplace(resultant, calculate_cost<M>(proj, r1.poly, r2.poly));
						}
					}
				} else {
					// hack
					for (auto it2_layer = it1_layer + 1; it2_layer < it->second.end(); ++it2_layer) {
						ordering.add_less(r1, it2_layer->root);
					}
				}

				for (auto it2 = it + 1; it2 != end; ++it2) {
					for (const auto& t_root2 : it2->second) {
						const auto& r2 = t_root2.root;

						const auto resultant = std::minmax(r1.poly, r2.poly);
						cov.emplace(resultant, std::make_pair(r1, r2));

						// make sure we only assign one index to each root
						if (!root_to_index.contains(r2)) {
							root_to_index.emplace(r2, n++);
						}

						// check if we already calculated the cost
						if (!costs.contains(resultant)) {
							costs.emplace(resultant, calculate_cost<M>(proj, r1.poly, r2.poly));
						}
					}
				}
			}
			closest = false;
		}
	};

	const auto& roots = delin.roots();
	const bool is_section = delin_interval.is_section();

	if (!delin_interval.lower_unbounded()) {
		const auto begin = boost::make_reverse_iterator(delin_interval.lower()) - 1;
		const auto end = boost::make_reverse_iterator(roots.begin());
		test(cov_below, layer_below, begin, end);
	}

	if (!delin_interval.upper_unbounded()) {
		const auto begin = delin_interval.upper();
		const auto end = roots.end();
		test(cov_above, layer_above, begin, end);
	}

	return std::make_tuple(cov_below, cov_above, layer_below, layer_above, costs, root_to_index);
}

inline auto construct_graph(const auto& cov_below, const auto& cov_above,
							const auto& costs, const auto& root_to_index) {
	const auto n = root_to_index.size() + 2;
	util::Graph graph(n);

	// create edge between dummy vertices
	boost::add_edge(0, 1, {0, 0}, graph);

	size_t edge_index = 1;
	for (const auto& [resultant, cost] : costs) {
		auto u = 0, v = 0;
		std::optional<util::RootPair> root_pair_below, root_pair_above;
		if (cov_below.contains(resultant)) {
			const auto& ir_pair = cov_below.at(resultant);
			u = root_to_index.at(ir_pair.second);
			root_pair_below = ir_pair;
		}
		if (cov_above.contains(resultant)) {
			const auto& ir_pair = cov_above.at(resultant);
			v = root_to_index.at(ir_pair.second);
			root_pair_above = ir_pair;
		}

		// add edge if it does not exist
		auto [edge_desc, exists] = boost::edge(u, v, graph);
		if (!exists) {
			const util::EdgeProperties edge_properties = {edge_index++,
														  cost,
														  root_pair_below,
														  root_pair_above};
			boost::add_edge(u, v, edge_properties, graph);
		} else {
			auto& edge = graph[edge_desc];
			if (cost < edge.weight) {
				edge.weight = cost;
				edge.root_pair_below = root_pair_below;
				edge.root_pair_above = root_pair_above;
			}
		}
	}

	auto modified_graph = graph;
	for (size_t u = 0; u < n; ++u) {
		const auto out_edges = boost::out_edges(u, graph);
		const auto min_edge = *std::min_element(
			out_edges.first, out_edges.second,
			[&graph](const auto& e1, const auto& e2) {
				return graph[e1].weight < graph[e2].weight;
			});

		// Add a new edge with double the weight of the minimum edge
		util::EdgeProperties edge_properties;
		edge_properties.index = edge_index++;
		edge_properties.weight = 2 * graph[min_edge].weight;
		edge_properties.root_pair_below = graph[min_edge].root_pair_below;
		edge_properties.root_pair_above = graph[min_edge].root_pair_above;

		boost::add_edge(u, u + n, edge_properties, modified_graph);
	}

	for (const auto& edge : boost::make_iterator_range(boost::edges(graph))) {
		const auto u = boost::source(edge, graph);
		const auto v = boost::target(edge, graph);
		boost::add_edge(n + u, n + v, {edge_index++, graph[edge].weight}, modified_graph);
	}

	return modified_graph;
}

inline std::string tagged_root_to_string(const datastructures::TaggedIndexedRoot& tagged_root) {
	std::stringstream ss;
	ss << tagged_root.root;
	return ss.str();
}

inline std::tuple<util::Graph, std::vector<util::Graph::edge_descriptor>, int> brute_force(const std::map<PolyPair, util::RootPair> cov_below,
																						   const std::map<PolyPair, util::RootPair> cov_above,
																						   std::map<PolyPair, util::RootPair> layer_below,
																						   std::map<PolyPair, util::RootPair> layer_above,
																						   const std::map<PolyPair, int>& costs,
																						   const std::map<datastructures::IndexedRoot, size_t>& root_to_index) {
	if (!layer_below.empty()) {
		// get first root in layer below
		const auto [res, roots] = *layer_below.begin();
		const auto [r1, r2] = roots;

		auto cov_below1 = cov_below;
		auto cov_below2 = cov_below;
		cov_below1[res] = std::make_pair(r1, r2);
		cov_below2[res] = std::make_pair(r2, r1);

		// remove first element from layer below
		layer_below.erase(layer_below.begin());

		const auto [graph1, matching_edges1, cost1] = brute_force(cov_below1, cov_above, layer_below, layer_above, costs, root_to_index);
		const auto [graph2, matching_edges2, cost2] = brute_force(cov_below2, cov_above, layer_below, layer_above, costs, root_to_index);

		if (cost1 < cost2) {
			return std::make_tuple(graph1, matching_edges1, cost1);
		} else {
			return std::make_tuple(graph2, matching_edges2, cost2);
		}
	}

	if (!layer_above.empty()) {
		// get first root in layer above
		const auto [res, roots] = *layer_above.begin();
		const auto [r1, r2] = roots;

		auto cov_above1 = cov_above;
		auto cov_above2 = cov_above;
		cov_above1[res] = std::make_pair(r1, r2);
		cov_above2[res] = std::make_pair(r2, r1);

		// remove first element from layer above
		layer_above.erase(layer_above.begin());

		const auto [graph1, matching_edges1, cost1] = brute_force(cov_below, cov_above1, layer_below, layer_above, costs, root_to_index);
		const auto [graph2, matching_edges2, cost2] = brute_force(cov_below, cov_above2, layer_below, layer_above, costs, root_to_index);

		if (cost1 < cost2) {
			return std::make_tuple(graph1, matching_edges1, cost1);
		} else {
			return std::make_tuple(graph2, matching_edges2, cost2);
		}
	}

	// solve minimum weight perfect matching problem
	const auto graph = construct_graph(cov_below, cov_above, costs, root_to_index);
	util::Matching matching(graph);
	const auto [matching_edges, cost] = matching.SolveMinimumCostPerfectMatching();
	return std::make_tuple(graph, matching_edges, cost);
};

template<ResultantCostMethod M>
inline void compute_optimal_ordering(auto& proj,
									 const auto& delin,
									 const auto& delin_interval,
									 const auto& interval,
									 auto& ordering,
									 auto& equational) {
	SMTRAT_TIME_START(start);

	const auto& roots = delin.roots();
	const bool is_section = delin_interval.is_section();

	if (delin.roots().empty()) {
		SMTRAT_LOG_DEBUG("smtrat.cadcells.representation", "No roots in delin");
		return;
	}

	if (!delin_interval.upper_unbounded()) {
		const auto end = is_section ? delin_interval.upper() + 1 : delin_interval.upper();
		for (auto it = delin.roots().end() - 1; it >= end; --it) {
			if (!it->second.empty()) {
				SMTRAT_LOG_DEBUG("smtrat.cadcells.representation",
								 boost::algorithm::join(it->second | boost::adaptors::transformed(tagged_root_to_string), ", "));
			}
		}
	}
	if (is_section) {
		SMTRAT_LOG_DEBUG("smtrat.cadcells.representation",
						 "---" << boost::algorithm::join(delin_interval.lower()->second | boost::adaptors::transformed(tagged_root_to_string), ", ") << "---");
	} else {
		SMTRAT_LOG_DEBUG("smtrat.cadcells.representation", "--- Sample point ---");
	}
	if (!delin_interval.lower_unbounded()) {
		const auto begin = is_section ? delin_interval.lower() - 1 : delin_interval.lower();
		for (auto it = begin; it >= delin.roots().begin(); --it) {
			if (!it->second.empty()) {
				SMTRAT_LOG_DEBUG("smtrat.cadcells.representation",
								 boost::algorithm::join(it->second | boost::adaptors::transformed(tagged_root_to_string), ", "));
			}
		}
	}

	const auto [cov_below, cov_above, layer_below, layer_above, costs, root_to_index] = get_candidate_resultants<M>(proj, delin, delin_interval, ordering);
	const auto [graph, matching_edges, cost] = brute_force(cov_below, cov_above, layer_below, layer_above, costs, root_to_index);

	// iterate over edges in matching and add the corresponding roots to the ordering
	auto ord = ordering;
	for (const auto& edge : matching_edges) {
		const auto u = boost::source(edge, graph);
		const auto v = boost::target(edge, graph);
		const auto edge_desc = boost::edge(u, v, graph).first;

		if (graph[edge_desc].root_pair_below) {
			const auto [r1, r2] = graph[edge_desc].root_pair_below.value();
			ord.add_less(r2, r1);
		}
		if (graph[edge_desc].root_pair_above) {
			const auto [r1, r2] = graph[edge_desc].root_pair_above.value();
			ord.add_less(r1, r2);
		}
	}

	if (is_section) {
		compute_optimal_equational_constraints<M>(proj,
												  ord,
												  equational,
												  interval.section_defining());
		for (const auto& [r1, r2, is_strict] : ord.data()) {
			for (const auto& poly : r1.polys()) {
				for (const auto& poly2 : r2.polys()) {
					if (!equational.contains(poly) && !equational.contains(poly2)) {
						ordering.add_less(r1, r2);
					}
				}
			}
		}
	} else {
		ordering = ord;
	}

	SMTRAT_TIME_FINISH(ordering_stats.ordering_timer, start);
	SMTRAT_STATISTICS_CALL(ordering_stats.ordering_costs.add(cost / 2));
	SMTRAT_LOG_DEBUG("smtrat.cadcells.representation", "Optimal ordering: " << ordering << " with cost " << cost / 2);
}

template<ResultantCostMethod M>
inline void compute_optimal_equational_constraints(auto& proj, const auto& ordering, auto& equational, const auto& section_defining) {
	const auto& ordering_less = ordering.less();
	if (ordering_less.contains(section_defining)) {
		const auto& section_defining_less = ordering_less.at(section_defining);
		for (const auto& root : section_defining_less) {
			if (!ordering_less.contains(root)) {
				for (const auto& poly : root.polys()) {
					equational.insert(poly);
				}
			}
		}
	}
	const auto& ordering_greater = ordering.greater();
	if (ordering_greater.contains(section_defining)) {
		const auto& section_defining_greater = ordering_greater.at(section_defining);
		for (const auto& root : section_defining_greater) {
			if (!ordering_greater.contains(root)) {
				for (const auto& poly : root.polys()) {
					equational.insert(poly);
				}
			}
		}
	}

	SMTRAT_LOG_DEBUG("smtrat.cadcells.representation", "Equational constraints: " << equational);
}

template<typename T, ResultantCostMethod M>
inline datastructures::CellRepresentation<T> compute_cell_optimal_ordering(datastructures::SampledDerivationRef<T>& der,
																		   LocalDelMode ldel_mode = LocalDelMode::NONE,
																		   bool enable_weak = false,
																		   bool use_global_cache = false,
																		   datastructures::IndexedRootOrdering global_ordering = datastructures::IndexedRootOrdering()) {
	datastructures::CellRepresentation<T> response(der);
	datastructures::Delineation reduced_delineation = der->delin();
	if (ldel_mode == LocalDelMode::ONLY_INDEPENDENT) {
		handle_local_del_simplify_non_independent(reduced_delineation);
	} else if (ldel_mode == LocalDelMode::SIMPLIFY) {
		handle_local_del_simplify_all(reduced_delineation);
	}
	auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
	response.description = util::compute_simplest_cell(der->proj(), reduced_cell, enable_weak);
	response.ordering = global_ordering;

	if (der->cell().is_section()) { // section case
		SMTRAT_LOG_DEBUG("smtrat.cadcells.representation", "Computing optimal ordering (section case).");
		handle_local_del_simplify_non_independent(reduced_delineation);
		handle_local_del(der, reduced_delineation, response);
		util::PolyDelineations poly_delins;
		util::decompose(reduced_delineation, reduced_cell, poly_delins);
		compute_optimal_ordering<M>(der->proj(),
									reduced_delineation,
									reduced_cell,
									response.description,
									response.ordering,
									response.equational);
	} else { // sector case
		SMTRAT_LOG_DEBUG("smtrat.cadcells.representation", "Computing optimal ordering (sector case).");
		handle_local_del(der, reduced_delineation, response);
		handle_cell_reduction(reduced_delineation, reduced_cell, response);
		compute_optimal_ordering<M>(der->proj(),
									reduced_delineation,
									reduced_cell,
									response.description,
									response.ordering,
									response.equational);
		handle_connectedness(der, response, enable_weak);
	}
	handle_ordering_polys(der, response);
	SMTRAT_STATISTICS_CALL(statistics().got_representation_equational(response.equational.size()));
	return response;
}

template<>
struct cell<CellHeuristic::OPTIMAL_FEATURE_BASED> {
	template<typename T>
	static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
		return compute_cell_optimal_ordering<T, ResultantCostMethod::FEATURE_BASED>(der);
	}
};

template<>
struct cell<CellHeuristic::OPTIMAL_NUM_MONOMIALS> {
	template<typename T>
	static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
		return compute_cell_optimal_ordering<T, ResultantCostMethod::NUM_MONOMIALS>(der);
	}
};

template<>
struct cell<CellHeuristic::OPTIMAL_NUM_RESULTANTS> {
	template<typename T>
	static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
		return compute_cell_optimal_ordering<T, ResultantCostMethod::NUM_RESULTANTS>(der);
	}
};

template<>
struct cell<CellHeuristic::OPTIMAL_NUM_VARIABLES> {
	template<typename T>
	static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
		return compute_cell_optimal_ordering<T, ResultantCostMethod::NUM_VARIABLES>(der);
	}
};

template<>
struct cell<CellHeuristic::OPTIMAL_SUM_OVER_TOTAL_DEGREE> {
	template<typename T>
	static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
		return compute_cell_optimal_ordering<T, ResultantCostMethod::SUM_OVER_TOTAL_DEGREE>(der);
	}
};

template<>
struct cell<CellHeuristic::OPTIMAL_TOTAL_DEGREE_EXACT> {
	template<typename T>
	static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
		return compute_cell_optimal_ordering<T, ResultantCostMethod::TOTAL_DEGREE_EXACT>(der);
	}
};

template<>
struct cell<CellHeuristic::OPTIMAL_TOTAL_DEGREE_UPPER_BOUND> {
	template<typename T>
	static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
		return compute_cell_optimal_ordering<T, ResultantCostMethod::TOTAL_DEGREE_UPPER_BOUND>(der);
	}
};

template<>
struct cell<CellHeuristic::OPTIMAL_VARIABLE_DEPTH> {
	template<typename T>
	static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
		return compute_cell_optimal_ordering<T, ResultantCostMethod::VARIABLE_DEPTH>(der);
	}
};

} // namespace smtrat::cadcells::representation
