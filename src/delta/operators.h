/**
 * @file operators.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <algorithm>
#include <cctype>
#include <functional>
#include <regex>
#include <sstream>
#include <utility>
#include <vector>

#include "Node.h"
#include "carl/io/streamingOperators.h"

namespace delta {
using carl::operator<<;

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
	NodeChangeSet res;
	if (!n.children.empty()) return res;
	if (n.name == "") return res;

	// Not a number
	std::regex number("[0-9]*\\.?[0-9]*");
	if (!std::regex_match(n.name, number)) return res;

	// Handle trailing dots
	std::regex trailingDot("[0-9]+\\.");
	if (std::regex_match(n.name, trailingDot)) {
		res.emplace_back(n.name.substr(0, n.name.size()-1), false);
		return res;
	}
	// Handle simple numbers
	std::regex simple("[0-9]+");
	if (std::regex_match(n.name, simple)) {
		if (n.name != "0") {
			res.emplace_back("0", false);
			if (n.name != "1") res.emplace_back("1", false);
		}
		for (unsigned i = 1; i < n.name.size(); i++) {
			res.emplace_back(n.name.substr(0, i), false);
		}
		return res;
	}

	// Handle degenerated floating points
	std::regex degenfloating("\\.[0-9]+");
	if (std::regex_match(n.name, degenfloating)) {
		res.emplace_back("0" + n.name, false);
		return res;
	}

	// Handle floating points
	std::regex floating("[0-9]+\\.[0-9]+");
	if (std::regex_match(n.name, floating)) {
		std::size_t pos = n.name.find('.');
		res.emplace_back(n.name.substr(0, pos), false);
		for (std::size_t i = pos + 2; i < n.name.size(); i++) {
			res.emplace_back(n.name.substr(0, i), false);
		}
		return res;
	}

	// Fallthrough
	return res;
}

}