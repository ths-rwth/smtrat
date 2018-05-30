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

#include "config.h"

#ifdef USE_BOOST_REGEX
#include "../cli/config.h"
#ifdef __VS
#pragma warning(push, 0)
#include <boost/regex.hpp>
#pragma warning(pop)
#else
#include <boost/regex.hpp>
#endif
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
 * Node operator that merges nodes with one of its own children.
 * @param n Node.
 * @return A set of replacements.
 */
NodeChangeSet mergeChild(const Node& n) {
	if (n.children.empty()) return NodeChangeSet();
	if ((n.name == "and") || (n.name == "or") || (n.name == "+") || (n.name == "*")) {
		NodeChangeSet res;
		for (auto it = n.children.begin(); it != n.children.end();) {
			std::vector<Node> newchildren;
			newchildren.insert(newchildren.end(), n.children.begin(), it);
			newchildren.insert(newchildren.end(), it->children.begin(), it->children.end());
			it++;
			if (it != n.children.end()) {
				newchildren.insert(newchildren.end(), it, n.children.end());
			}
			res.emplace_back(std::make_tuple(n.name, newchildren, n.brackets));
		}
		return res;
	}
	return NodeChangeSet();
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
		res.emplace_back(n.name.substr(0, n.name.size()-1));
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
	if (n.children.size() < 2) return NodeChangeSet();
	Node cur = n.children[1];
	for (const auto& v: n.children[0].children) {
		cur = cur.clone(v.name, &v.children[0]);
	}
	res.push_back(cur);
	return res;
}

NodeChangeSet BV_zeroExtend(const Node& n) {
	if (n.name != "") return NodeChangeSet();
	if (n.children.size() != 2) return NodeChangeSet();
	const Node& op = n.children[0];
	const Node& arg = n.children[1];
	if (op.name != "_") return NodeChangeSet();
	if (op.children.size() != 2) return NodeChangeSet();
	if (op.children[0].name != "zero_extend") return NodeChangeSet();
	if (arg.name != "_") return NodeChangeSet();
	if (arg.children.size() != 2) return NodeChangeSet();
	
	std::size_t ext = std::stoul(op.children[1].name);
	std::size_t index = std::stoul(arg.children[1].name);
	
	NodeChangeSet res;
	res.push_back(Node("_", { arg.children[0], Node(std::to_string(index+ext), false) }));
	return res;
}

/**
 * (bvlshr 
 *   (bvlshr x (_ bv1 8)) 
 *   (_ bv1 8)
 * )
 */
NodeChangeSet BV_mergeShift(const Node& n) {
	if (n.name == "bvshl" || n.name == "bvlshr") {
		if (n.children.size() != 2) return NodeChangeSet();
		const Node& c = n.children[0];
		// Same operation
		if (c.name != n.name) return NodeChangeSet();
		if (c.children.size() != 2) return NodeChangeSet();
		if (c.children[1].name != "_") return NodeChangeSet();
		if (c.children[1].children.size() != 2) return NodeChangeSet();
		if (n.children[1].name != "_") return NodeChangeSet();
		if (n.children[1].children.size() != 2) return NodeChangeSet();
		// Same bit-width
		if (c.children[1].children[1].name != n.children[1].children[1].name) return NodeChangeSet();
		if (!regex_match(n.children[1].children[0].name, regex("bv[0-9]+"))) return NodeChangeSet();
		if (!regex_match(c.children[1].children[0].name, regex("bv[0-9]+"))) return NodeChangeSet();
		
		std::size_t inner = std::stoul(c.children[1].children[0].name.substr(2));
		std::size_t outer = std::stoul(n.children[1].children[0].name.substr(2));
		
		NodeChangeSet res;
		res.push_back(Node(n.name, { c.children[0], Node("_", { Node("bv" + std::to_string(inner + outer), false), n.children[1].children[1] }) }));
		return res;
	}
	return NodeChangeSet();
}

}
