/**
 * @file operators.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <algorithm>
#include <cctype>
#include <functional>
#include <sstream>
#include <utility>
#include <vector>

#include "Node.h"

namespace delta {

/// Set of new nodes.
typedef std::vector<Node> NodeChangeSet;
/**
 * Type of an node operator.
 * A NodeOperator is called on a node and shall return a set of new nodes.
 * These new nodes are supposed to be a simplifying replacement for the given node.
 */
typedef std::function<NodeChangeSet(const Node&)> NodeOperator;

/**
 * Node operator that returns all children of a node.
 * @param n Node.
 * @return All children of n.
 */
NodeChangeSet children(const Node& n) {
	return n.children;
}

/**
 * Node operator that provides meaningful replacements for numbers.
 * @param n Node.
 * @return A set of numbers.
 */
NodeChangeSet number(const Node& n) {
	if (!n.children.empty()) return NodeChangeSet();
	if (n.name == "") return NodeChangeSet();
	for (auto it: n.name) {
		if (isdigit(it)) continue;
		if (it == '.') continue;
		return NodeChangeSet();
	}
	NodeChangeSet res;
	if (n.name != "0" && n.name != "1") {
		res.emplace_back("0");
		res.emplace_back("1");
	}
	for (unsigned i = 1; i < n.name.size(); i++) {
		res.emplace_back(n.name.substr(0, i));
	}
	return res;
}

}