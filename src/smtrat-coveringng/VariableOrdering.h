#pragma once

#include <carl-arith/core/Variable.h>
#include <carl-formula/formula/Formula.h>
#include <carl-formula/formula/functions/Variables.h>
#include <smtrat-common/types.h>

#include "types.h"

#include <smtrat-mcsat/variableordering/VariableOrdering.h>

namespace smtrat::covering_ng::variables {

/**
 * @brief Possible heuristics for variable ordering.
 */
enum VariableOrderingHeuristics {
	GreedyMaxUnivariate,
	FeatureBased,
	FeatureBasedZ3,
	FeatureBasedBrown,
	FeatureBasedTriangular,
	FeatureBasedLexicographic,
	FeatureBasedPickering,
	EarliestSplitting,
};

inline std::string get_name(VariableOrderingHeuristics ordering) {
	switch (ordering) {
	case GreedyMaxUnivariate:
		return "GreedyMaxUnivariate";
	case FeatureBased:
		return "FeatureBased";
	case FeatureBasedZ3:
		return "FeatureBasedZ3";
	case FeatureBasedBrown:
		return "FeatureBasedBrown";
	case FeatureBasedTriangular:
		return "FeatureBasedTriangular";
	case FeatureBasedLexicographic:
		return "FeatureBasedLexicographic";
	case FeatureBasedPickering:
		return "FeatureBasedPickering";
	case EarliestSplitting:
		return "EarliestSplitting";
	default:
		return "";
	}
}

namespace impl {

using carl::operator<<;

/**
 * @brief Calculates a variable ordering based on the given quantifier blocks and the given formula.
 * @tparam vo The variable ordering heuristic to use.
 * @param quantifiers The quantifier blocks (Variables in a block can be exchanged, blocks can not be exchanged)
 * @param formula Formula to calculate the variable ordering for.
 * @return Variable ordering.
 * @details The variable ordering is calculated as follows:
 * 1. Calculate the variable ordering for the formula as if there were no quantifiers. This is done by calling mcsat::calculate_variable_order<vo>(constraints). In code this is called the unblocked variable ordering
 * 2. Sort the variables in the unblocked variable ordering by the quantifier block they are in. The order of the quantifier blocks is the same as in the vector quantifiers. Use a stable sort such that the order of the variables in a quantifier block is not changed.
 * 3. Return the resulting vector.
 */
template<mcsat::VariableOrdering vo>
inline std::vector<carl::Variable> variable_ordering(const carl::QuantifierPrefix& quantifiers, const FormulaT& formula) {
	boost::container::flat_map<carl::Variable, size_t> quantifier_block_index;
	for (auto v : formula.variables()) {
		if (std::find_if(quantifiers.begin(), quantifiers.end(), [v](const auto& e) { return e.second == v; }) == quantifiers.end()) {
			quantifier_block_index[v] = 0;
		}
	}
	std::size_t i = 0;
	if (!quantifier_block_index.empty()) i++;
	carl::Quantifier last = carl::Quantifier::FREE;
	for (const auto& e : quantifiers) {
		assert(e.first != carl::Quantifier::FREE);
		if (last != e.first && last != carl::Quantifier::FREE) i++;
		quantifier_block_index[e.second] = i;
	}


	//1. Calculate the unblocked variable ordering
	std::vector<ConstraintT> constraints;
	carl::arithmetic_constraints(formula, constraints);
	std::vector<carl::Variable> result = mcsat::calculate_variable_order<vo>(constraints);
	SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Unblocked variable order: " << result);

	//2. Sort the variables in the unblocked variable ordering by the quantifier block they are in.
	std::stable_sort(result.begin(), result.end(), [&quantifier_block_index](const auto& lhs, const auto& rhs) {
		return quantifier_block_index.at(lhs) < quantifier_block_index.at(rhs);
	});

	SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Resulting variable order: " << result);
	return result;
}

/**
 * @brief Calculates a variable ordering based on the given quantifier blocks and the given formula. Heuristic such that the formula can be split as early as possible
 * @param quantifiers The quantifier blocks (Variables in a block can be exchanged, blocks can not be exchanged)
 * @param base_formula Formula to calculate the variable ordering for.
 * @return Variable ordering.
 * @details The variable ordering is calculated as follows:
 * 1. Identify the first opportunity to split the formula. This is the first time that the formula is not an atom and not a negation of an atom. If there is no such opportunity, return some other variable ordering.
 * 2. For each pairwise combination of subformulas, calculate the set of shared variables
 * 3. Iterate over the quantifier blocks and for each block, sort the variables by the number of occurrences in the sets of shared variables and the size of the smallest set of shared variables in which the variable occurs.
 * If the heuristic is inconclusive, sort the remaining variables of this block by some other variable ordering
 * 4. Return the resulting vector.
 */
inline std::vector<carl::Variable> sort_earliest_splitting(const carl::QuantifierPrefix& prefix, const FormulaT& base_formula) {
	//Check if the formula can be split at all ->  if not return some other variable ordering
	//subformulas will otherwise contain the subformulas of tge formula the first time it can potentially be split
	std::vector<FormulaT> subformulas;
	FormulaT formula = base_formula;
	while (subformulas.empty()) {
		if (formula.is_atom()) {
			// No splitting possible at all -> return some other variable ordering
			return impl::variable_ordering<mcsat::VariableOrdering::FeatureBasedBrown>(prefix, base_formula);
		}
		if (formula.type() == carl::FormulaType::NOT) {
			formula = formula.subformula();
		} else {
			assert(formula.is_nary());
			subformulas = formula.subformulas();
		}
	}

	std::vector<boost::container::flat_set<carl::Variable>> quantifiers;
	quantifiers.emplace_back();
	for (auto v : base_formula.variables()) {
		if (std::find_if(prefix.begin(), prefix.end(), [v](const auto& e) { return e.second == v; }) == prefix.end()) {
			quantifiers.back().insert(v);
		}
	}
	if (quantifiers.back().empty()) quantifiers.pop_back();
	carl::Quantifier last = carl::Quantifier::FREE;
	for (const auto& e : prefix) {
		assert(e.first != carl::Quantifier::FREE);
		if (last != e.first && last != carl::Quantifier::FREE) quantifiers.emplace_back();
		quantifiers.back().insert(e.second);
	}

	//For each pairwise combination of subformulas, calculate the set of shared variables
	std::vector<carl::Variables> shared_subformula_variables;
	for (size_t i = 0; i < subformulas.size() - 1; i++) {
		for (size_t j = i + 1; j < subformulas.size(); j++) {
			auto& lhs = subformulas[i].variables();
			auto& rhs = subformulas[j].variables();
			carl::Variables shared;
			std::set_intersection(lhs.begin(), lhs.end(), rhs.begin(), rhs.end(), std::inserter(shared, shared.begin()));
			shared_subformula_variables.push_back(shared);
		}
	}

	//Helper function to delete a variable from all sets of shared variables
	auto deleteVariable = [&shared_subformula_variables](const carl::Variable& var) -> void {
		for (auto& shared : shared_subformula_variables) {
			shared.erase(var);
		}
		//delete empty sets
		shared_subformula_variables.erase(std::remove_if(shared_subformula_variables.begin(), shared_subformula_variables.end(), [](const auto& set) { return set.empty(); }), shared_subformula_variables.end());
	};

	// Helper function to return a pair of number of occurrences and size of smallest set of shared variables in which this variable occurs
	auto getInfo = [&shared_subformula_variables](const carl::Variable& var) -> std::pair<size_t, size_t> {
		size_t num_occurrences = 0;
		size_t min_shared_size = std::numeric_limits<size_t>::max();
		for (const auto& shared : shared_subformula_variables) {
			if (shared.find(var) != shared.end()) {
				num_occurrences++;
				min_shared_size = std::min(min_shared_size, shared.size());
			}
		}
		return std::make_pair(num_occurrences, min_shared_size);
	};

	// resulting variable ordering
	std::vector<carl::Variable> result;

	//Used in case that the heuristic is inconclusive
	std::vector<ConstraintT> constraints;
	carl::arithmetic_constraints(formula, constraints);
	auto unblocked_sorting = mcsat::variableordering::greedy_max_univariate(constraints);

	for (const auto& block : quantifiers) {
		auto block_variables = block;
		while(!block_variables.empty()) {
			std::map<carl::Variable, std::pair<size_t, size_t>> variables_by_info;
			for (const auto& var : block_variables) {
				auto info = getInfo(var);
				variables_by_info[var] = info;
			}
			SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Variables by info: " << variables_by_info)
			// iterate over the keys
			std::pair<size_t, size_t> max_info = std::make_pair(std::numeric_limits<size_t>::min(), std::numeric_limits<size_t>::max());
			carl::Variable max_var = carl::Variable::NO_VARIABLE;
			for (const auto& [var, info] : variables_by_info) {
				if (info.first > max_info.first) {
					max_info = info;
					max_var = var;
				} else if (info.first == max_info.first) {
					if (info.second < max_info.second) {
						max_info = info;
						max_var = var;
					}
				}
			}
			SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Max var: " << max_var << " with info " << max_info)
			if(max_var == carl::Variable::NO_VARIABLE){
				//Sort the remaining variables of this block by some other variable ordering
				for(const auto& var : unblocked_sorting){
					if(block_variables.contains(var)){
						result.push_back(var);
						deleteVariable(var);
						block_variables.erase(var);
					}
				}
				break;
			}
			//add the variable to the result
			result.push_back(max_var);
			//delete the variable from all sets of shared variables and remove it from the current quantifier block
			deleteVariable(max_var);
			block_variables.erase(max_var);
		}
	}

	SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Resulting variable order: " << result);

	assert(result.size() == formula.variables().size());

	return result;

} // namespace impl

} // namespace impl

template<VariableOrderingHeuristics vo>
inline std::vector<carl::Variable> get_variable_ordering(const carl::QuantifierPrefix& quantifiers, const FormulaT& formula) {
	switch (vo) {
	case GreedyMaxUnivariate:
		return impl::variable_ordering<mcsat::VariableOrdering::GreedyMaxUnivariate>(quantifiers, formula);
	case FeatureBased:
		return impl::variable_ordering<mcsat::VariableOrdering::FeatureBased>(quantifiers, formula);
	case FeatureBasedZ3:
		return impl::variable_ordering<mcsat::VariableOrdering::FeatureBasedZ3>(quantifiers, formula);
	case FeatureBasedBrown:
		return impl::variable_ordering<mcsat::VariableOrdering::FeatureBasedBrown>(quantifiers, formula);
	case FeatureBasedTriangular:
		return impl::variable_ordering<mcsat::VariableOrdering::FeatureBasedTriangular>(quantifiers, formula);
	case FeatureBasedLexicographic:
		return impl::variable_ordering<mcsat::VariableOrdering::FeatureBasedLexicographic>(quantifiers, formula);
	case FeatureBasedPickering:
		return impl::variable_ordering<mcsat::VariableOrdering::FeatureBasedPickering>(quantifiers, formula);
	case EarliestSplitting:
		return impl::sort_earliest_splitting(quantifiers, formula);
	}
}

} // namespace smtrat::covering_ng::variables