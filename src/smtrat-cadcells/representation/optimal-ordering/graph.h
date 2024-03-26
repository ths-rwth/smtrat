#pragma once

#include <optional>

#include <boost/graph/adjacency_list.hpp>

#include "../../datastructures/roots.h"

namespace smtrat::cadcells::representation::util {

typedef std::pair<datastructures::IndexedRoot, datastructures::IndexedRoot> RootPair;

struct EdgeProperties {
	size_t index;
	int weight;
	std::optional<RootPair> root_pair_below, root_pair_above;
};

typedef boost::adjacency_list<boost::vecS,
							  boost::vecS,
							  boost::undirectedS,
							  boost::no_property,
							  EdgeProperties>
	Graph;

} // namespace smtrat::cadcells::representation::util
