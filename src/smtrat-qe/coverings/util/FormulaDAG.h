#pragma once

#include "smtrat-common/types.h"
#include <carl-arith/constraint/BasicConstraint.h>
#include <carl-formula/formula/Formula.h>
#include <functional>
#include <initializer_list>
#include <optional>
#include <stack>
#include <type_traits>
#include <vector>

namespace smtrat::qe::coverings::util {

/**
 * @brief Class to represent a node in the Formula-DAG
 * @details The Formula-DAG is a DAG that represents a formula. Each node in the DAG represents a subformula of the formula.
 * The root node represents the formula itself. The children of a node are the subformulas of the node.
 * The Formula-DAG is used to walk through the formula and compute the results for each node.
 * @example The formula (a & b) | (c & d) is represented by the following Formula-DAG:
 * OR (root) with two children: AND (child 1) and AND (child 2)
 * The first AND has two children: a (child 1) and b (child 2)
 * The second AND has two children: c (child 1) and d (child 2)
 */
class FormulaNode {
	// A Node represents the basic structure for representing a formula -> Implicitly represents a DAG
private:
	mutable size_t m_hash = 0;
	mutable carl::FormulaType m_type;
	std::vector<FormulaNode> m_children;
	const FormulaT& m_currentFormula;

public:
	explicit FormulaNode(const FormulaT& formula) : m_type(formula.type()), m_currentFormula(formula) {
		if(formula.is_atom()){
			return;
		}
		if (formula.type() == carl::FormulaType::FORALL || formula.type() == carl::FormulaType::EXISTS) {
			m_children.emplace_back(formula.quantified_formula());
			return;
		}
		if (formula.type() == carl::FormulaType::NOT) {
			m_children.emplace_back(formula.subformula());
			return;
		}
		if (formula.is_nary()) {
			for (const auto& subformula : formula.subformulas()) {
				m_children.emplace_back(subformula);
			}
			return;
		}
		assert(false && "Unhandled case in Node constructor");
	}

	[[nodiscard]] carl::FormulaType getType() const {
		return m_type;
	}

	void setType(carl::FormulaType type) const {
		m_type = type;
		// Change in node -> invalidate hash
		m_hash = 0;
	}

	[[nodiscard]] const auto& getChildren() const {
		return m_children;
	}

	[[nodiscard]] const FormulaNode* getChild(std::size_t index) const {
		return &m_children[index];
	}

	[[nodiscard]] FormulaNode* getChild(std::size_t index) {
		return &m_children[index];
	}

	[[nodiscard]] const FormulaT& getFormula() const {
		return m_currentFormula;
	}

	/**
	 * @brief Computes the hash for the node
	 * @return Hash for the node
	 * @details Return cached hash if available, otherwise compute the hash and store it. The hash is computed based on the type of the node and the hashes of the children.
	 */
	size_t hash() const {
		if (m_hash != 0) {
			return m_hash;
		}

		boost::hash_combine(m_hash, m_type);
		boost::hash_combine(m_hash, getFormula().hash());
		boost::hash_combine(m_hash, getFormula().id());

		for (const auto& child : m_children) {
			boost::hash_combine(m_hash, child.hash());
		}
		return m_hash;
	}
};

} // namespace smtrat::qe::coverings::util

namespace std {
template<>
struct hash<smtrat::qe::coverings::util::FormulaNode> {
	std::size_t operator()(const smtrat::qe::coverings::util::FormulaNode& node) const {
		return node.hash();
	}
};

} // namespace std

namespace smtrat::qe::coverings::util {

inline bool operator==(const FormulaNode& lhs, const FormulaNode& rhs) {
	return std::hash<FormulaNode>()(lhs) == std::hash<FormulaNode>()(rhs);
}

inline std::ostream& operator<<(std::ostream& os, const FormulaNode& node) {
	if (node.getType() == carl::FormulaType::AND) {
		os << "AND(";
		for (const auto& child : node.getChildren()) {
			os << child << " ";
		}
		os << ")";
	} else if (node.getType() == carl::FormulaType::OR) {
		os << "OR(";
		for (const auto& child : node.getChildren()) {
			os << child << " ";
		}
		os << ")";
	} else if (node.getType() == carl::FormulaType::NOT) {
		os << "NOT(";
		for (const auto& child : node.getChildren()) {
			os << child << " ";
		}
		os << ")";
	} else if (node.getType() == carl::FormulaType::IMPLIES) {
		os << "IMPLIES(";
		for (const auto& child : node.getChildren()) {
			os << child << " ";
		}
		os << ")";
	} else if (node.getType() == carl::FormulaType::IFF) {
		os << "IFF(";
		for (const auto& child : node.getChildren()) {
			os << child << " ";
		}
		os << ")";
	} else if (node.getType() == carl::FormulaType::XOR) {
		os << "XOR(";
		for (const auto& child : node.getChildren()) {
			os << child << " ";
		}
		os << ")";
	} else if (node.getType() == carl::FormulaType::FORALL) {
		os << "FORALL(";
		for (const auto& child : node.getChildren()) {
			os << child << " ";
		}
		os << ")";
	} else if (node.getType() == carl::FormulaType::EXISTS) {
		os << "EXISTS(";
		for (const auto& child : node.getChildren()) {
			os << child << " ";
		}
		os << ")";
	} else {
		os << node.getFormula();
	}
	return os;
}

inline std::ostream& operator<<(std::ostream& os, const std::vector<FormulaNode>& nodes) {
	os << "[";
	for(size_t i = 0 ; i < nodes.size() - 1 ; i++){
		os << nodes[i] << ", " ;
	}
	os << nodes.back() << "]";
	return os;
}

/**
 * @brief Helper class to walk through the Formula-DAG and compute the results for each node
 * @tparam OutputType
 * @details The DAG is traversed in a depth-first manner, the results for each node are stored in a map. The results for the children of a node are computed before the result for the node itself.
 * For each formula type of interest a handler function can be registered. This function is then called for each node of the corresponding type.
 * The return type of the handler function must be the same as the template parameter OutputType.
 * The handler function is called with the current node as argument. The results for the children of the node can be accessed via the function getChildResults.
 * The result for the current Node of the Formula-DAG can then be calculated and stored via the function setResult.
 */
template<typename OutputType>
class FormulaTransformer {

private:
	/// Stack to store the nodes that have to be processed; first: the node; second: a boolean that indicates whether the children have been expanded/processed
	std::stack<std::pair<FormulaNode*, bool>> m_stack;
	/// Root node of the DAG
	FormulaNode m_root;
	/// Map to store the results for each node
	std::unordered_map<FormulaNode, OutputType> m_node_results;
	/// Map to store the handlers for each type
	std::map<carl::FormulaType, std::function<OutputType(const FormulaNode&)>> m_node_handlers;
	/// Map to store the nodes for each formula
	std::map<FormulaT, FormulaNode*> m_formula_nodes;

public:
	FormulaTransformer() = delete;
	explicit FormulaTransformer(const FormulaT& formula)
		: m_root(formula) {}

	[[nodiscard]] const FormulaNode& getRoot() const {
		return m_root;
	}

	/**
	 * @brief Returns the result for the root node. If the root has not been processed yet, the DAG is traversed and the results are computed
	 * @return Tranformation result for the root node
	 */
	OutputType& getResult() {
		if (!m_node_results.contains(m_root)) {
			SMTRAT_LOG_TRACE("smtrat.qe.coverings", "Computing results for " << m_root)
			// The root has not been processed yet
			// Starts the walk through the DAG
			m_stack.emplace(&m_root, false);
			process_stack();
		}
		return m_node_results[m_root];
	}

	std::unordered_map<FormulaNode, OutputType>& getResults() {
		if (!m_node_results.contains(m_root)) {
			SMTRAT_LOG_TRACE("smtrat.qe.coverings", "Computing results for " << m_root)
			// The root has not been processed yet
			// Starts the walk through the DAG
			m_stack.emplace(&m_root, false);
			process_stack();
		}
		return m_node_results;
	}

	FormulaNode* getNodeFromFormula(const FormulaT& formula) {
		//Traverse the DAG to find the node with the given formula
		if(m_formula_nodes.find(formula) != m_formula_nodes.end()) {
			return m_formula_nodes[formula];
		}

		std::stack<FormulaNode*> stack;
		stack.push(&m_root);
		while (!stack.empty()) {
			FormulaNode* node = stack.top();
			stack.pop();
			if (node->getFormula() == formula) {
				m_formula_nodes[formula] = node;
				return node;
			}
			for(size_t i = 0; i < node->getChildren().size(); i++) {
				stack.push(node->getChild(i));
			}
		}
		assert(false && "Formula not found in DAG");
	}

protected:

	/**
	 * @brief Registers a handler for the given formula type
	 * @param types List of formula types for which the handler should be registered
	 * @param handler Function that is called for each node of the given type. Return type must be the same as the template parameter OutputType.
	 */
	void registerHandler(std::initializer_list<carl::FormulaType> types, std::function<OutputType(const FormulaNode&)> handler) {
		for (const auto& type : types) {
			assert(m_node_handlers.find(type) == m_node_handlers.end() && "Handler for this type already registered");
			m_node_handlers.emplace(type, handler);
		}
	}

	OutputType& getChildResults(const FormulaNode& node, std::size_t index) {
		return m_node_results[*node.getChild(index)];
	}

	/**
	 * @brief Used to access the result for the given node, useful for the handler functions to access the child results
	 * @param node
	 * @return Returns the result for the given node
	 */
	OutputType& getResult(const FormulaNode& node) {
		return m_node_results[node];
	}


	void setResult(const FormulaNode& node, const OutputType& result) {
		m_node_results[node] = result;
	}

private:
	/**
	 * @brief Pushes the node to the stack and all its children
	 * @param node
	 */
	void push_with_children_to_stack(FormulaNode& node) {
		m_stack.emplace(&node, true);
		for (std::size_t i = 0; i < node.getChildren().size(); ++i) {
			m_stack.emplace(node.getChild(i), false);
		}
	}

	/**
	 * @brief Computes the result for the given node, Asserts that a handler for the type of the node is registered
	 * @param node
	 * @details This function assumes that the children of the node have already been processed, the registered handler function is then called with the current node as argument
	 */
	void compute_node_result(FormulaNode& node) {
		// Based on the current type of the node -> transform the formula and store it in the node
		// This function assumes that the children of the node have already been processed
		SMTRAT_LOG_TRACE("smtrat.qe.coverings", "Computing result for node " << node << " of type " << node.getType());

		if (m_node_results.find(node) != m_node_results.end()) {
			SMTRAT_LOG_TRACE("smtrat.qe.coverings", "Node " << node << " has already been processed");
			return;
		}

		assert(m_node_handlers.find(node.getType()) != m_node_handlers.end() && "No handler for this type registered:");
		m_node_results[node] = m_node_handlers[node.getType()](node);
		SMTRAT_LOG_TRACE("smtrat.qe.coverings", "Result for node " << node << " is " << m_node_results[node]);
	}

	/**
	 * @brief Processes the stack
	 * @details Empties the stack by processing every node in it, This is done in two steps:
	 * 1. A node is expanded and all its children are pushed to the stack
	 * 2. Once all children are processed, the node is processed
	 */
	void process_stack() {
		while (!m_stack.empty()) {
			auto& [node, was_expanded] = m_stack.top();
			m_stack.pop();
			if (was_expanded) {
				compute_node_result(*node);
			} else {
				push_with_children_to_stack(*node);
			}
		}
	}
};

template<typename OutputType>
inline std::ostream& operator<<(std::ostream& os, const FormulaTransformer<OutputType>& walker) {
	os << walker.getRoot();
	return os;
}

} // namespace smtrat::qe::coverings::util
