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

#define USE_BOOST_REGEX
#ifdef USE_BOOST_REGEX
#include <boost/regex.hpp>
using boost::regex;
using boost::regex_match;
#else
#include <regex>
using std::regex;
using std::regex_match;
#endif

#include "Node.h"
#include "utils.h"

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
 * @return A set of replacements.
 */
NodeChangeSet children(const Node& n) {
	if (n.name == "let") return NodeChangeSet();
	return n.children;
}

/**
 * Node operator that provides meaningful replacements for numbers.
 * @param n Node.
 * @return A set of replacements.
 */
NodeChangeSet number(const Node& n) {
	if (!n.children.empty()) return NodeChangeSet();
	if (n.name == "") return NodeChangeSet();
	if (n.brackets) return NodeChangeSet();

	NodeChangeSet res;

	// Not a number
	if (!regex_match(n.name, regex("[0-9]*\\.?[0-9]*"))) return res;

	// Handle trailing dot -> remove dot
	if (regex_match(n.name, regex("[0-9]+\\."))) {
		res.emplace_back(n.name.substr(0, n.name.size()-1), false);
		return res;
	}
	// Handle simple numbers -> remove last digits
	if (regex_match(n.name, regex("[0-9]+"))) {
		for (unsigned i = 1; i < n.name.size(); i++) {
			res.emplace_back(n.name.substr(0, i), false);
		}
		return res;
	}

	// Handle degenerated floating points -> add zero in front
	if (regex_match(n.name, regex("\\.[0-9]+"))) {
		res.emplace_back("0" + n.name, false);
		return res;
	}

	// Handle floating points -> remove decimal places
	if (regex_match(n.name, regex("[0-9]+\\.[0-9]+"))) {
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

/**
 * Node operator that provides meaningful replacements for variables.
 * @param n Node.
 * @return A set of replacements.
 */
NodeChangeSet constant(const Node& n) {
	if (!n.children.empty()) return NodeChangeSet();
	if (n.name == "") return NodeChangeSet();
	if (n.brackets) return NodeChangeSet();
	if (n.name == "0" || n.name == "1" || n.name == "true" || n.name == "false") return NodeChangeSet();
	if (n.name == "Bool" || n.name == "Int" || n.name == "Real") return NodeChangeSet();
	NodeChangeSet res;
	res.emplace_back("0", false);
	res.emplace_back("1", false);
	res.emplace_back("true", false);
	res.emplace_back("false", false);
	return res;
}

/**
 * Node operator that eliminated let expressions.
 * @param n Node.
 * @return A set of replacements.
 */
NodeChangeSet letExpression(const Node& n) {
	if (n.name != "let") return NodeChangeSet();
	NodeChangeSet res;
	Node cur = n.children[1];
	for (const auto& v: n.children[0].children) {
		cur = cur.clone(v.name, &v.children[0]);
	}
	res.push_back(cur);
	return res;
}

}