/**
 * @file Node.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <numeric>
#include <iostream>
#include <utility>
#include <vector>

#include "utils.h"

namespace delta {

/**
 * This class represents a node in a SMTLIB file.
 *
 * Every syntactical constructor is represented by a node.
 * A node may have a name and may have several children.
 * In a file, this corresponds to `(<name> <child> <child>...)`.
 *
 * Note that these nodes are constructed by a parser that has no semantic knowledge of the smtlib format.
 * Hence, the data representable by these nodes is only a very rough overapproximation of the actual smtlib format.
 */
struct Node {
	/// Name of the node.
	std::string name;
	/// Children of the node.
	std::vector<Node> children;
	/// Flag if the node was contained in brackets.
	bool brackets;

	/**
	 * Create an empty node.
	 */
	explicit Node(): brackets(false) {}
	/**
	 * Create a node with a name.
	 * @param name Name of the node.
	 * @param brackets If not is contained in brackets.
	 */
	explicit Node(const std::string& name, bool brackets = true): name(name), brackets(brackets) {}
	/**
	 * Create a node with a name.
	 * @param data Tuple containing the name and the brackets flag.
	 */
	explicit Node(const std::tuple<std::string, bool>& data): name(std::get<0>(data)), brackets(std::get<1>(data)) {}
	/**
	 * Create a node with children.
	 * @param data Tuple containing the children and the brackets flag.
	 */
	explicit Node(const std::tuple<std::vector<Node>, bool>& data): children(std::get<0>(data)), brackets(std::get<1>(data)) {}
	/**
	 * Create a node with a name and children.
	 * @param data Tuple containing the name, the children and the brackets flag.
	 */
	explicit Node(const std::tuple<std::string, std::vector<Node>, bool>& data): name(std::get<0>(data)), children(std::get<1>(data)), brackets(std::get<2>(data)) {}

	/**
	 * Streaming operator.
	 * This operator should output a representation that is syntactically identically to the one that was parsed.
	 * @param os Output stream.
	 * @param n Node.
	 * @return `os`.
	 */
	friend inline std::ostream& operator<<(std::ostream& os, const Node& n) {
		if (n.brackets) os << "(";
		os << n.name;
		for (auto c: n.children) {
			if (n.name == "") os << c << std::endl;
			else os << " " << c;
		}
		if (n.brackets) os << ")";
		return os;
	}
	
	/**
	 * Calculates the number of nodes.
     * @return Number of nodes.
     */
	unsigned complexity() const {
		return std::accumulate(children.begin(), children.end(), (unsigned)1, [](unsigned a, const Node& b){ return a + b.complexity(); });
	}
	/**
	 * Checks if this node is immutable.
	 * This method implements simple checks to prevent unnecessary solver errors if essential parts of the smtlib file are removed, for example the `set-logic` statement.
     * @return If node may be removed.
     */
	bool immutable() const {
		if (name == "set-logic") return true;
		if (name == "set-info") return true;
		return false;
	}
	/**
	 * Returns a string representation of this node.
     * @return String of the node.
     */
	std::string repr(bool longRepr = false) const {
		if (longRepr) return String() << *this;
		if (name != "") return name;
		return "Node";
	}
	
	/**
	 * Clone this node recursively.
	 * If the node `from` is encountered, replace it with `to`. If `to` is a nullptr, remove it instead.
     * @param from Node to replace.
     * @param to Node to replace with.
     * @return Cloned node.
     */
	Node clone(const Node* from, const Node* to) const {
		std::vector<Node> newChildren;
		for (auto& c: children) {
			if (&c == from) {
				if (to != nullptr) newChildren.push_back(*to);
			} else {
				newChildren.push_back(c.clone(from, to));
			}
		}
		return Node(std::make_tuple(name, newChildren, brackets));
	}
};

}