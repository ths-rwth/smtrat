#pragma once

#include "matching.h"

namespace smtrat::cadcells::representation::util {

inline std::pair<std::vector<Graph::edge_descriptor>, int> calculate_minimum_weight_edge_cover(const Graph& graph) {
	const size_t num_vertices = boost::num_vertices(graph);
	size_t num_edges = boost::num_edges(graph);

	Graph modified_graph = graph;
	boost::unordered_map<Graph::edge_descriptor, Graph::edge_descriptor> edge_map;
	for (size_t u = 0; u < num_vertices; ++u) {
		const auto new_edge = boost::add_edge(u, num_vertices + u, num_edges++, modified_graph).first;

		// For each vertex v in the original graph, find an incident edge with minimum cost
		boost::put(boost::edge_weight, modified_graph, new_edge, -1);
		int min_cost = -1;
		Graph::edge_descriptor min_edge;
		for (const auto& edge : boost::make_iterator_range(boost::out_edges(u, graph))) {
			const int edge_cost = boost::get(boost::edge_weight, graph, edge);
			if (edge_cost < min_cost || min_cost == -1) {
				min_cost = edge_cost;
				min_edge = edge;
			}
		}

		boost::put(boost::edge_weight, modified_graph, new_edge, 2 * min_cost);
		edge_map.insert(std::make_pair(new_edge, min_edge));
	}

	for (const auto& edge : boost::make_iterator_range(boost::edges(graph))) {
		const auto u = boost::source(edge, graph);
		const auto v = boost::target(edge, graph);
		const auto edge_cost = boost::get(boost::edge_weight, graph, edge);

		const auto new_edge = boost::add_edge(num_vertices + u, num_vertices + v, num_edges++, modified_graph).first;
		boost::put(boost::edge_weight, modified_graph, new_edge, edge_cost);
	}

	Matching matching(modified_graph);
	const auto solution = matching.SolveMinimumCostPerfectMatching();
	const auto matching_edges = solution.first;

	std::vector<Graph::edge_descriptor> edge_cover;
	for (const auto& edge : matching_edges) {
		const auto& mapped_edge = edge_map.find(edge);
		if (mapped_edge != edge_map.end()) {
			edge_cover.push_back(mapped_edge->second);
		} else {
			const auto u = boost::source(edge, graph);
			const auto v = boost::target(edge, graph);
			if (u < num_vertices && v < num_vertices) {
				edge_cover.push_back(edge);
			}
		}
	}

	return std::make_pair(edge_cover, solution.second / 2);
}

} // namespace smtrat::cadcells::representation::util
