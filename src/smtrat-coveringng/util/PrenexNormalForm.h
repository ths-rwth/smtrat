#pragma once

#include "FormulaDAG.h"
#include "smtrat-common/types.h"
#include "smtrat-coveringng/VariableOrdering.h"
#include <algorithm>
#include <carl-arith/core/Common.h>
#include <carl-formula/formula/FormulaContent.h>
#include <functional>
#include <memory>
#include <ostream>
#include <unordered_map>

// Helper class to transform the used formula in prenex normal form

namespace smtrat::covering_ng::util {


inline Poly replacePoly(const Poly& original, const std::map<carl::Variable, carl::Variable>& oldToNew) {
	// Construct the same polynomial, but replace the variables according to the map
	// check if Poly is class MultivariatePolynomial<...>
	if constexpr (std::is_same<Poly, carl::MultivariatePolynomial<Rational>>::value) {
		Poly::TermsType newTerms;
		for (const auto& used_term : original.terms()) {
			SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Used term: " << used_term)
			if (used_term.is_constant()) {
				newTerms.emplace_back(used_term.coeff());
				continue;
			}
			std::vector<std::pair<carl::Variable, std::size_t>> newExponents;
			for (const auto& [var, exponent] : used_term.monomial()->exponents()) {
				auto it = oldToNew.find(var);
				if (it != oldToNew.end()) {
					newExponents.emplace_back(it->second, exponent);
				} else {
					newExponents.emplace_back(var, exponent);
				}
			}
			std::sort(newExponents.begin(), newExponents.end(), [](const auto& lhs, const auto& rhs) { return lhs.first < rhs.first; });
			assert(std::is_sorted(newExponents.begin(), newExponents.end(), [](const auto& lhs, const auto& rhs) { return lhs.first < rhs.first; }));
			auto newMonomial = carl::MonomialPool::getInstance().create(std::move(newExponents));
			newTerms.emplace_back(used_term.coeff(), std::move(newMonomial));
		}
		return Poly(newTerms);
	}

	SMTRAT_LOG_FATAL("smtrat.covering_ng", "Cant replace variables of polynomial with type: " << typeid(Poly).name() << "!")
	assert(false && "Cant replace variables of polynomial with this type!");
}

inline FormulaT renameAtom(const FormulaT& original, const std::map<carl::Variable, carl::Variable>& oldToNew) {
	switch (original.type()) {
	case carl::FormulaType::CONSTRAINT:
		return FormulaT(ConstraintT(replacePoly(original.constraint().lhs(), oldToNew), original.constraint().relation()));
	case carl::FormulaType::BOOL:
		return original;
	default:
		SMTRAT_LOG_ERROR("smtrat.covering_ng", "Cant rename variables of formula with type: " << original.type())
		return FormulaT(carl::FormulaType::FALSE);
	}
}

inline FormulaT renameVariables(const FormulaT& original, const std::map<carl::Variable, carl::Variable>& oldToNew) {
	assert((original.type() != carl::FormulaType::FORALL && original.type() != carl::FormulaType::EXISTS) && "Invalid formula type!");
	// Build the exact same formula again, but replace the variables according to the map
	if (original.is_atom()) {
		return renameAtom(original, oldToNew);
	}
	if (original.type() == carl::FormulaType::NOT) {
		return FormulaT(carl::FormulaType::NOT, renameVariables(original.subformula(), oldToNew));
	}
	if (original.is_nary()) {
		std::vector<FormulaT> subformulas;
		for (const auto& item : original.subformulas()) {
			subformulas.emplace_back(renameVariables(item, oldToNew));
		}
		return FormulaT(original.type(), std::move(subformulas));
	}

	SMTRAT_LOG_FATAL("smtrat.covering_ng", "Cant rename variables of formula with type: " << original.type())
	assert(false);
}


class PrenexNormalFormConverter : public FormulaTransformer<std::pair<std::vector<variables::QuantifierBlock>, FormulaT>>{

	// Handlers for the different cases for prenex normal form

private :

	/*
     * @brief Handles the case of a quantifier node. Only add the quantifier if the variable actually occurs in the formula
     * I.e. forall x y. f(x) -> forall x. f(x)
	 */
	std::pair<std::vector<variables::QuantifierBlock>, FormulaT> handle_quantifiers(const FormulaNode& node) {
		assert(node.getChildren().size() == 1 && "A quantifier node must have exactly one child!");
		assert((node.getQuantifiedVariables().mType == VariableQuantificationType::EXISTS || node.getQuantifiedVariables().mType == VariableQuantificationType::FORALL) && "The quantifier is not correctly set!");
		auto [child_quantifiers, child_formula] = getChildResults(node, 0);
		carl::Variables alreadyQuantifiedVariables;
		for (const auto& quantifier : child_quantifiers) {
			alreadyQuantifiedVariables.insert(quantifier.mVariables.begin(), quantifier.mVariables.end());
		}
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Already quantified variables: " << alreadyQuantifiedVariables)
		// Gather all variables used by the formula -> only these variables can be quantified
		auto usedFormulaVariables = child_formula.variables();
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Used variables in inner Formula: " << usedFormulaVariables)
		auto newQuantifiedVariables = node.getQuantifiedVariables().mVariables;
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "New quantified variables: " << newQuantifiedVariables)
		carl::Variables newVariables_tmp;
		std::set_intersection(newQuantifiedVariables.begin(), newQuantifiedVariables.end(), usedFormulaVariables.begin(), usedFormulaVariables.end(), std::inserter(newVariables_tmp, newVariables_tmp.begin()));

		// remove all variables that are already quantified
		carl::Variables newVariables;
		std::set_difference(newVariables_tmp.begin(), newVariables_tmp.end(), alreadyQuantifiedVariables.begin(), alreadyQuantifiedVariables.end(), std::inserter(newVariables, newVariables.begin()));

		SMTRAT_LOG_TRACE("smtrat.covering_ng", "New quantified variables: " << newVariables)
		// if newVariables is empty the inner quantifiers already quantify all variables and this quantifier can be removed
		if (newVariables.empty()) {
			return std::make_pair(child_quantifiers, child_formula);
		}
		//if the quantifier type is the same as the last one just add the variables to the last quantifier
		if (!child_quantifiers.empty() && child_quantifiers.front().mType == node.getQuantifiedVariables().mType) {
			for(const auto& var : newVariables){
				child_quantifiers.front().addVariable(var);
			}
			return std::make_pair(child_quantifiers, child_formula);
		}
		variables::QuantifierBlock quantifiedVariables(newVariables, node.getQuantifiedVariables().mType);
		child_quantifiers.insert(child_quantifiers.begin(), std::move(quantifiedVariables));
		return std::make_pair(child_quantifiers, child_formula);
	}

	std::pair<std::vector<variables::QuantifierBlock>, FormulaT> handle_and_or(const FormulaNode& node) {
		const carl::FormulaType node_type = node.getType();
		assert(node.getChildren().size() >= 2 && "An AND/OR node must have at least two children!");
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Processing AND/OR node with " << node.getChildren().size() << " children, of type: " << node_type)
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Children: " << node.getChildren())
		// Placeholders for the result
		std::vector<variables::QuantifierBlock> quantifiers_result;
		FormulaT formulas_result = FormulaT(node_type == carl::FormulaType::AND ? carl::FormulaType::TRUE : carl::FormulaType::FALSE);

		// For every child_node store the quantified variables and the free variables
		std::unordered_map<FormulaNode, carl::Variables> quantified_variables_per_child;
		std::unordered_map<FormulaNode, carl::Variables> free_variables_per_child;
		for (const auto& child : node.getChildren()) {
			const auto& [child_quantifiers, child_formula] = getResult(child);
			carl::Variables quantified_variables;
			carl::Variables free_variables;
			for (const auto& quantifier : child_quantifiers) {
				quantified_variables.insert(quantifier.mVariables.begin(), quantifier.mVariables.end());
			}
			for (const auto& variable : child_formula.variables()) {
				if (!quantified_variables.contains(variable)) {
					free_variables.insert(variable);
				}
			}
			quantified_variables_per_child[child] = quantified_variables;
			free_variables_per_child[child] = free_variables;
		}

		// Iterate over all children and check if the current quantified variables intersect with any other quantified variable or free variable of any other formula -> if so rename this variable in the current formula
		std::unordered_map<FormulaNode, carl::Variables> variables_to_rename_per_child;
		for (const auto& child : node.getChildren()) {
			const auto& current_quantified_variables = quantified_variables_per_child[child];
			carl::Variables otherVariables;
			for (const auto& other_child : node.getChildren()) {
				if (other_child == child) {
					continue;
				}
				const auto& other_quantified_variables = quantified_variables_per_child[other_child];
				const auto& other_free_variables = free_variables_per_child[other_child];
				carl::Variables otherVariables_tmp;
				std::set_union(other_quantified_variables.begin(), other_quantified_variables.end(), other_free_variables.begin(), other_free_variables.end(), std::inserter(otherVariables_tmp, otherVariables_tmp.begin()));
				otherVariables.insert(otherVariables_tmp.begin(), otherVariables_tmp.end());
			}
			carl::Variables variables_to_rename;
			std::set_intersection(current_quantified_variables.begin(), current_quantified_variables.end(), otherVariables.begin(), otherVariables.end(), std::inserter(variables_to_rename, variables_to_rename.begin()));
			variables_to_rename_per_child[child] = variables_to_rename;
		}

		// Iterate over all children and do the actual renaming
		for (const auto& child : node.getChildren()) {
			const auto& [child_quantifiers, child_formula] = getResult(child);
			const auto& toRename = variables_to_rename_per_child[child];
			SMTRAT_LOG_TRACE("smtrat.covering_ng", "Child Quantifiers: " << child_quantifiers)
			SMTRAT_LOG_TRACE("smtrat.covering_ng", "Child Formula: " << child_formula)
			SMTRAT_LOG_TRACE("smtrat.covering_ng", "Variables to rename: " << toRename)
			if (toRename.empty()) {
				SMTRAT_LOG_TRACE("smtrat.covering_ng", "No variables to rename in child")
				quantifiers_result.insert(quantifiers_result.begin(), child_quantifiers.begin(), child_quantifiers.end());
				auto tmp = FormulaT(node_type, formulas_result, child_formula);
				formulas_result = std::move(tmp);
				SMTRAT_LOG_TRACE("smtrat.covering_ng", "Current Quantifiers: " << quantifiers_result)
				SMTRAT_LOG_TRACE("smtrat.covering_ng", "Current Formula: " << formulas_result)
				continue;
			}
			//Right now there is no need to store the rename_map for later use
			//As only quantified variables are being renamed and the quantifiers do not matter for the potential satisfying model
			std::map<carl::Variable, carl::Variable> rename_map;
			for (const auto& variable : toRename) {
				rename_map[variable] = carl::fresh_real_variable(); // TODO: Use some sort of naming scheme, based on the original variable name
			}
			const FormulaT renamed_formula = renameVariables(child_formula, rename_map);
			auto quantifier_cpy = child_quantifiers;
			for (auto& quantifier : quantifier_cpy) {
				quantifier.renameVariables(rename_map);
			}
			SMTRAT_LOG_TRACE("smtrat.covering_ng", "Renamed Quantifiers: " << quantifier_cpy)
			SMTRAT_LOG_TRACE("smtrat.covering_ng", "Renamed Formula: " << renamed_formula)
			quantifiers_result.insert(quantifiers_result.begin(), quantifier_cpy.begin(), quantifier_cpy.end());
			auto tmp = FormulaT(node_type, formulas_result, renamed_formula);
			formulas_result = std::move(tmp);
			SMTRAT_LOG_TRACE("smtrat.covering_ng", "Current Quantifiers: " << quantifiers_result)
			SMTRAT_LOG_TRACE("smtrat.covering_ng", "Current Formula: " << formulas_result)
		}

		return std::make_pair(std::move(quantifiers_result), std::move(formulas_result));
	}
	std::pair<std::vector<variables::QuantifierBlock>, FormulaT> handle_not(const FormulaNode& node) {
		assert(node.getChildren().size() == 1 && "A NOT node must have exactly one child!");
		// get child result
		auto [child_quantifier, child_formula] = getChildResults(node, 0);
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Current Quantifiers: " << child_quantifier)
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Current Formula: " << child_formula)
		// invert all the child_quantifier and negate the formula
		for (auto& quantifier : child_quantifier) {
			quantifier.invertQuantifier();
		}
		auto negated_formula = child_formula.negated();
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Negated Quantifiers: " << child_quantifier)
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Negated Formula: " << negated_formula)
		return std::make_pair(child_quantifier, negated_formula);
	}

	std::pair<std::vector<variables::QuantifierBlock>, FormulaT> handle_implies(const FormulaNode& node) {
		assert(node.getChildren().size() == 2 && "An IMPLIES node must have exactly two children!");
		// a => b == !a || b

		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Current Node: " << node)
		auto [child_quantifier, child_formula] = getChildResults(node, 0);
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Negating first child: " << child_quantifier << " " << child_formula)
		for (auto& quantifier : child_quantifier) {
			quantifier.invertQuantifier();
		}
		auto negated_formula = child_formula.negated();
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Negated first child: " << child_quantifier << " " << negated_formula)
		// store a
		setResult(*node.getChild(0), std::make_pair(child_quantifier, negated_formula));

		//Current node: (!a => b) So we need to change the Formula type of the current node to OR
		node.setType(carl::FormulaType::OR);

		//Resolve potential name clashes
		return handle_and_or(node);
	}


public :

	explicit PrenexNormalFormConverter(const FormulaT& formula) : FormulaTransformer(formula){
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Converting formula to prenex normal form: " << formula)
		//Registering the Handlers
		registerHandler({carl::FormulaType::AND, carl::FormulaType::OR}, [this](const auto& node){ return handle_and_or(node); });
		registerHandler({carl::FormulaType::NOT}, [this](const auto& node){ return handle_not(node); });
		registerHandler({carl::FormulaType::IMPLIES}, [this](const auto& node){ return handle_implies(node); });
		registerHandler({carl::FormulaType::EXISTS, carl::FormulaType::FORALL}, [this](const auto& node){ return handle_quantifiers(node); });
		registerHandler({carl::FormulaType::TRUE, carl::FormulaType::FALSE, carl::FormulaType::CONSTRAINT, carl::FormulaType::BOOL}, [](const auto& node){return std::make_pair(std::vector<variables::QuantifierBlock>(), node.getFormula());});
		//TODO: IFF and XOR
	}

};

} // namespace smtrat::covering_ng::util