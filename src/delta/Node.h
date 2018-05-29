/**
 * @file Node.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <numeric>
#include <iostream>
#include <set>
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
	std::size_t size;

	/**
	 * Create an empty node.
	 */
	explicit Node(): brackets(false), size(1) {}
	/**
	 * Create a node with a name.
	 * @param name Name of the node.
	 * @param brackets If not is contained in brackets.
	 */
	explicit Node(const std::string& name, bool brackets = true): name(name), brackets(brackets), size(1) {}
	/**
	 * Create a node with a name.
	 * @param data Tuple containing the name and the brackets flag.
	 */
	explicit Node(const std::tuple<std::string, bool>& data): name(std::get<0>(data)), brackets(std::get<1>(data)), size(1) {}
	/**
	 * Create a node with children.
	 * @param data Tuple containing the children and the brackets flag.
	 */
	explicit Node(const std::tuple<std::vector<Node>, bool>& data): children(std::get<0>(data)), brackets(std::get<1>(data)), size(0) {
		recalculateSize();
	}
	/**
	 * Create a node with a name and children.
	 * @param data Tuple containing the name, the children and the brackets flag.
	 */
	explicit Node(const std::tuple<std::string, std::vector<Node>, bool>& data): name(std::get<0>(data)), children(std::get<1>(data)), brackets(std::get<2>(data)), size(0) {
		recalculateSize();
	}
	
	explicit Node(const std::string& name, const std::initializer_list<Node>& children, bool brackets = true): name(name), children(children), brackets(brackets), size(0) {
		recalculateSize();
	}
	
	void recalculateSize() {
		size = std::accumulate(children.begin(), children.end(), (std::size_t)1, [](std::size_t a, const Node& b){ return a + b.complexity(); });
	}
	
	/**
	 * Calculates the number of nodes.
     * @return Number of nodes.
     */
	std::size_t complexity() const {
		return size;
	}
	/**
	 * Checks if this node is immutable.
	 * This method implements simple checks to prevent unnecessary solver errors if essential parts of the smtlib file are removed, for example the `set-logic` statement.
     * @return If node may be removed.
     */
	bool immutable() const {
		if (name == "set-logic") return true;
		return false;
	}
	/**
	 * Returns a string representation of this node.
     * @return String of the node.
     */
	std::string repr(bool longRepr = false) const {
		if (longRepr) return String() << *this;
		if (name == "_") {
			assert(children.size() == 2);
			return children[0].repr(longRepr) + "_" + children[1].repr(longRepr);
		}
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
		if (this == from) return *to;
		std::vector<Node> newChildren;
		for (const auto& c: children) {
			if (&c == from) {
				if (to != nullptr) newChildren.push_back(*to);
			} else {
				newChildren.push_back(c.clone(from, to));
			}
		}
		return Node(std::make_tuple(name, newChildren, brackets));
	}

	/**
	 * Clone this node recursively.
	 * If a node with name `from` without children is enountered, replace it with `to`.
	 * @param from Node name to replace.
	 * @param to Node to replace with.
	 * @return Cloned node.
	 */
	Node clone(const std::string& from, const Node* to) const {
		if (children.size() == 0 && name == from) return *to;
		std::vector<Node> newChildren;
		for (const auto& c: children) {
			if (c.children.size() == 0 &&  c.name == from) {
				if (to != nullptr) newChildren.push_back(*to);
			} else {
				newChildren.push_back(c.clone(from, to));
			}
		}
		return Node(std::make_tuple(name, newChildren, brackets));
	}
	
	void collectNames(std::set<std::string>& names) const {
		if (name == "declare-fun") return;
		names.insert(name);
		for (const auto& c: children) c.collectNames(names);
	}
	
	void eliminateDefineFuns() {
		std::set<std::string> names;
		collectNames(names);
		for (auto it = children.begin(); it != children.end(); ) {
			if (it->name == "declare-fun") {
				if (names.count(it->children[0].name) == 0) {
					children.erase(it);
					continue;
				}
			}
			it++;
		}
		recalculateSize();
	}
};

template<bool pretty>
struct NodePrinter {
	const Node& node;
	NodePrinter(const Node& n): node(n) {}
	void print(std::ostream& os, const Node& n) const {
		if (n.name == "" && !n.brackets) {
			for (auto c: n.children) {
				print(os, c);
				os << std::endl;
			}
			return;
		}
		if (n.brackets) os << "(";
		os << n.name;
		for (auto c: n.children) {
			os << " ";
			print(os, c);
		}
		if (n.brackets) os << ")";
	}
	
	void pretty_print(std::ostream& os, const Node& n, std::string indent = "") const {
		bool pretty_this = (n.name != "set-logic") && (n.name != "declare-fun");
		if (!pretty_this) {
			print(os, n);
			return;
		}
		if (n.name == "" && !n.brackets) {
			for (auto c: n.children) {
				pretty_print(os, c, indent);
				os << std::endl;
			}
			return;
		}
		
		if (n.brackets) os << "(";
		os << n.name;
		if (n.brackets && !n.children.empty()) os << std::endl;
		for (auto c: n.children) {
			os << indent << "\t";
			pretty_print(os, c, indent + "\t");
			if (n.brackets) os << std::endl;
		}
		if (n.brackets) os << indent << ")";
	}
};

/**
 * Streaming operator.
 * This operator should output a representation that is syntactically identically to the one that was parsed.
 * @param os Output stream.
 * @param n Node.
 * @return `os`.
 */
inline std::ostream& operator<<(std::ostream& os, const Node& n) {
	if (n.brackets) os << "(";
	os << n.name;
	for (auto c: n.children) {
		if (n.name == "") os << c << (n.brackets ? ' ' : '\n');
		else os << " " << c;
	}
	if (n.brackets) os << ")";
	return os;
}

template<bool pretty>
inline std::ostream& operator<<(std::ostream& os, const NodePrinter<pretty>& np) {
	if (pretty) {
		np.pretty_print(os, np.node);
	} else {
		np.print(os, np.node);
	}
	return os;
}

}
