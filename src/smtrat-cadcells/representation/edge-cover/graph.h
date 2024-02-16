#pragma once

#include <boost/graph/adjacency_list.hpp>

namespace smtrat::cadcells::representation::util {

typedef boost::adjacency_list<boost::vecS,
							  boost::vecS,
							  boost::undirectedS,
							  boost::no_property,
							  boost::property<boost::edge_index_t, int, boost::property<boost::edge_weight_t, int>>>
	Graph;

} // namespace smtrat::cadcells::representation::util
