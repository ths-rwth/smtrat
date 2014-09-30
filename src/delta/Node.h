/**
 * @file Node.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <iostream>
#include <utility>
#include <vector>

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
	 * Create an empty node that may be contained in brackets.
	 * @param brackets If not is contained in brackets.
	 */
	explicit Node(bool brackets): brackets(brackets) {}
	/**
	 * Create a node with a name.
	 * @param name Name of the node.
	 * @param brackets If not is contained in brackets.
	 */
	explicit Node(const std::string& name, bool brackets = true): name(name), brackets(brackets) {}
	/**
	 * Create a node with children.
	 * @param children Children of the node.
	 * @param brackets If not is contained in brackets.
	 */
	explicit Node(const std::vector<Node>& children, bool brackets = true): children(children), brackets(brackets) {}
	/**
	 * Create a node with a name and children.
	 * @param name Name of the node.
	 * @param children Children of the node.
	 * @param brackets If not is contained in brackets.
	 */
	explicit Node(const std::string& name, const std::vector<Node>& children, bool brackets = true): name(name), children(children), brackets(brackets) {}
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

	friend inline std::ostream& operator<<(std::ostream& out, const Node& n);
	
	/**
	 * Calculates the number of nodes.
     * @return Number of nodes.
     */
	unsigned complexity() const {
		unsigned sum = 1;
		for (auto c: children) sum += c.complexity();
		return sum;
	}
	/**
	 * Checks if this node may be removed.
	 * This method implements simple checks to prevent unnecessary solver errors if essential parts of the smtlib file are removed, for example the `set-logic` statement.
     * @return If node may be removed.
     */
	bool removable() const {
		if (name == "set-logic") return false;
		if (name == "set-info") return false;
		return true;
	}
	/**
	 * Returns a short name of this node, usually the name.
     * @return Short name of the node.
     */
	std::string shortName() const {
		if (name != "") return name;
		return "Node";
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
		if (n.name == "") os << c << std::endl;
		else os << " " << c;
	}
	if (n.brackets) os << ")";
	return os;
}

}

namespace std {

/**
 * Implementation of `std::swap` for Node objects.
 * @param lhs First node.
 * @param rhs Second node.
 */
void swap(delta::Node& lhs, delta::Node& rhs) {
	std::swap(lhs.name, rhs.name);
	std::swap(lhs.children, rhs.children);
	std::swap(lhs.brackets, rhs.brackets);
}

}