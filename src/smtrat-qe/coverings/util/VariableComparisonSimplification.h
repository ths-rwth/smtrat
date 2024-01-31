#pragma once

#include "FormulaDAG.h"

namespace smtrat::qe::coverings::util {

inline std::optional<VariableComparisonT> convertToVarCompareIfPossible(const FormulaT& formula) {
	SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Trying to convert Formula: " << formula)
	if (formula.type() != carl::FormulaType::CONSTRAINT) {
		SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Formula is not a constraint.")
		return std::nullopt;
	}
	auto& constraint = formula.constraint();
	auto vars = carl::variables(constraint.lhs());
	if (vars.size() != 1) {
		SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Constraint is not univariate.")
		return std::nullopt;
	}
	if (constraint.lhs().degree(*vars.begin()) > 1) {
		SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Constraint is not linear.")
		return std::nullopt;
	}

	bool negative = constraint.lhs().lcoeff() < 0 ;
	return VariableComparisonT(constraint.lhs().single_variable(), VariableComparisonT::RAN(-constraint.lhs().normalize().constant_part()), negative ? turn_around(constraint.relation()) : constraint.relation());
}

inline std::optional<carl::Relation> compare(const std::variant<VariableComparisonT::MR, VariableComparisonT::RAN>& lhs, const std::variant<VariableComparisonT::MR, VariableComparisonT::RAN>& rhs) {
	if (holds_alternative<VariableComparisonT::MR>(lhs) && holds_alternative<VariableComparisonT::MR>(rhs)) {
		// both are multivariate roots
		auto& lhs_value = std::get<MultivariateRootT>(lhs);
		auto& rhs_value = std::get<MultivariateRootT>(rhs);
		if (lhs_value.var() != rhs_value.var() || lhs_value.poly() != rhs_value.poly()) {
			// not comparable
			return std::nullopt;
		}
		if (lhs_value.k() < rhs_value.k()) {
			return carl::Relation::LESS;
		}
		if (lhs_value.k() > rhs_value.k()) {
			return carl::Relation::GREATER;
		}
		return carl::Relation::EQ;
	}

	if (holds_alternative<VariableComparisonT::RAN>(lhs) && holds_alternative<VariableComparisonT::RAN>(rhs)) {
		// both are RANS
		auto& lhs_value = std::get<VariableComparisonT::RAN>(lhs);
		auto& rhs_value = std::get<VariableComparisonT::RAN>(rhs);
		if (lhs_value < rhs_value) {
			return carl::Relation::LESS;
		}
		if (lhs_value > rhs_value) {
			return carl::Relation::GREATER;
		}
		return carl::Relation::EQ;
	}
	return std::nullopt;
}

inline std::optional<FormulaT> simplifyRelationVariableComparison(const carl::FormulaType& parent_relation, const VariableComparisonT& lhs, const VariableComparisonT& rhs) {
	assert(parent_relation == carl::FormulaType::OR || parent_relation == carl::FormulaType::AND);
	if (lhs.relation() == rhs.relation() && lhs.value() == rhs.value()) {
		// lhs == rhs
		return FormulaT(lhs);
	}
	auto lhs_relation = lhs.relation();
	auto rhs_relation = rhs.relation();
	auto& lhs_value = lhs.value();
	auto& rhs_value = rhs.value();
	auto comparison_result = compare(lhs_value, rhs_value);
	SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Checking if " << lhs << " and " << rhs << " are comparable.")
	if (!comparison_result) {
		// lhs_value and rhs_value are not comparable
		SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Not comparable")
		return std::nullopt;
	} else {
		SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Comparison Result:  " << comparison_result)
	}
	if (parent_relation == carl::FormulaType::AND) {
		if (lhs_relation == carl::Relation::LESS) {
			switch (rhs_relation) {
			case carl::Relation::LESS:
			case carl::Relation::LEQ:
				// var < lhs_value && var < rhs_value -> var < min(lhs_value, rhs_value)
				if (comparison_result == carl::Relation::EQ || comparison_result == carl::Relation::LESS) {
					// lhs is less or eq
					return FormulaT(rhs);
				}
				// rhs is less
				return FormulaT(lhs);

			case carl::Relation::EQ:
				// var < lhs_value && var = rhs_value
				//  -> var = rhs_value if rhs_value < lhs_value
				//  -> false otherwise
				if (comparison_result == carl::Relation::GREATER) {
					// lhs > rhs -> var = rhs_value
					// i.e. x < 5 && x = 3 -> x = 3
					return FormulaT(rhs);
				}
				// lhs <= rhs -> false
				return FormulaT(carl::FormulaType::FALSE);

			case carl::Relation::GREATER:
				// var < lhs_value && var > rhs_value
				// no simplification if lhs_value > rhs_value
				// false otherwise
				if (comparison_result == carl::Relation::GREATER) {
					// no simplification
					return std::nullopt;
				}
				return FormulaT(carl::FormulaType::FALSE);

			case carl::Relation::GEQ:
				// var < lhs_value && var >= rhs_value
				// lhs_value = rhs_value -> var = lhs_value
				// lhs_value < rhs_value -> false
				// lhs_value > rhs_value -> no simplifications
				if (comparison_result == carl::Relation::EQ) {
					return FormulaT(VariableComparisonT(lhs.var(), lhs_value, carl::Relation::EQ, false));
				} else if (comparison_result == carl::Relation::LESS) {
					return FormulaT(carl::FormulaType::FALSE);
				} else {
					return std::nullopt;
				}
			case carl::Relation::NEQ:
				// var < lhs_value && var != rhs_value
				// lhs_value <= rhs_value -> var < lhs_value
				// lhs > rhs_value -> no simplifications
				if (comparison_result == carl::Relation::LESS || comparison_result == carl::Relation::EQ) {
					return FormulaT(lhs);
				}
				return std::nullopt;
			}
		} else if (lhs_relation == carl::Relation::LEQ) {
			switch (rhs_relation) {
			case carl::Relation::LESS:
				// handled symmetric case
				return std::nullopt;
			case carl::Relation::LEQ:
				// var <= lhs_value && var <= rhs_value -> var <= min(lhs_value, rhs_value)
				if (comparison_result == carl::Relation::LESS || comparison_result == carl::Relation::EQ) {
					return FormulaT(lhs);
				}
				return FormulaT(rhs);
			case carl::Relation::EQ:
				// var <= lhs_value && var = rhs_value
				// lhs_value < rhs_value -> false
				// lhs_value >= rhs_value -> var = rhs_value
				if (comparison_result == carl::Relation::LESS) {
					return FormulaT(carl::FormulaType::FALSE);
				}
				return FormulaT(rhs);
			case carl::Relation::GREATER:
				// var <= lhs_value && var > rhs_value
				// lhs_value <= rhs_value -> false
				// lhs_value > rhs_value -> no simplifications
				if (comparison_result == carl::Relation::LESS || comparison_result == carl::Relation::EQ) {
					return FormulaT(carl::FormulaType::FALSE);
				}
				return std::nullopt;
			case carl::Relation::GEQ:
				// var <= lhs_value && var >= rhs_value
				// lhs_value = rhs_value -> var = lhs_value
				// lhs_value < rhs_value -> false
				// lhs_value > rhs_value -> no simplifications
				if (comparison_result == carl::Relation::EQ) {
					return FormulaT(VariableComparisonT(lhs.var(), lhs_value, carl::Relation::EQ, false));
				}
				if (comparison_result == carl::Relation::LESS) {
					return FormulaT(carl::FormulaType::FALSE);
				}
				return std::nullopt;
			case carl::Relation::NEQ:
				// var <= lhs_value && var != rhs_value
				// lhs_value = rhs_value -> var < lhs_value
				// lhs_value < rhs_value -> var <= lhs_value
				// lhs_value > rhs_value -> no simplifications
				if (comparison_result == carl::Relation::EQ) {
					return FormulaT(VariableComparisonT(lhs.var(), lhs_value, carl::Relation::LESS, false));
				}
				if (comparison_result == carl::Relation::LESS) {
					return FormulaT(lhs);
				}
				return std::nullopt;
			}
		} else if (lhs_relation == carl::Relation::EQ) {
			switch (rhs_relation) {
			case carl::Relation::LESS:
			case carl::Relation::LEQ:
				// handled symmetric case
				return std::nullopt;
			case carl::Relation::EQ:
				// var = lhs_value && var = rhs_value
				// lhs_value = rhs_value -> var = lhs_value
				// otherwise -> false
				if (comparison_result == carl::Relation::EQ) {
					return FormulaT(lhs);
				}
				return FormulaT(carl::FormulaType::FALSE);
			case carl::Relation::GREATER:
				// var = lhs_value && var > rhs_value
				// lhs_value <= rhs_value -> false
				// lhs_value > rhs_value -> x > rhs_value
				if (comparison_result == carl::Relation::LESS || comparison_result == carl::Relation::EQ) {
					return FormulaT(carl::FormulaType::FALSE);
				}
				return FormulaT(rhs);
			case carl::Relation::GEQ:
				// var = lhs_value && var >= rhs_value
				// lhs_value = rhs_value -> var = lhs_value
				// lhs_value < rhs_value -> false
				// lhs_value > rhs_value -> x > rhs_value
				if (comparison_result == carl::Relation::EQ) {
					return FormulaT(lhs);
				}
				if (comparison_result == carl::Relation::LESS) {
					return FormulaT(carl::FormulaType::FALSE);
				}
				return FormulaT(rhs);
			case carl::Relation::NEQ:
				// var = lhs_value && var != rhs_value
				// lhs_value = rhs_value -> false
				// otherwise -> no simplifications
				if (comparison_result == carl::Relation::EQ) {
					return FormulaT(carl::FormulaType::FALSE);
				}
				return std::nullopt;
			}
		} else if (lhs_relation == carl::Relation::GREATER) {
			switch (rhs_relation) {
			case carl::Relation::LESS:
			case carl::Relation::LEQ:
			case carl::Relation::EQ:
				// handled symmetric cases
				return std::nullopt;
			case carl::Relation::GREATER:
			case carl::Relation::GEQ:
				// var > lhs_value && var >(=) rhs_value
				// lhs_value >= rhs_value -> var > lhs_value
				// lhs_value < rhs_value -> var > rhs_value
				if (comparison_result == carl::Relation::GREATER || comparison_result == carl::Relation::EQ) {
					return FormulaT(lhs);
				}
				return FormulaT(rhs);
			case carl::Relation::NEQ:
				// var > lhs_value && var != rhs_value
				// lhs_value >= rhs_value -> var > lhs_value
				// lhs_value < rhs_value -> no simplifications
				if (comparison_result == carl::Relation::GREATER || comparison_result == carl::Relation::EQ) {
					return FormulaT(lhs);
				}
				return std::nullopt;
			}
		} else if (lhs_relation == carl::Relation::GEQ) {
			switch (rhs_relation) {
			case carl::Relation::LESS:
			case carl::Relation::LEQ:
			case carl::Relation::EQ:
			case carl::Relation::GREATER:
				// handled symmetric cases
				return std::nullopt;
			case carl::Relation::GEQ:
				// var >= lhs_value && var >= rhs_value
				// lhs_value >= rhs_value -> var >= lhs_value
				// lhs_value < rhs_value -> var >= rhs_value
				if (comparison_result == carl::Relation::GREATER || comparison_result == carl::Relation::EQ) {
					return FormulaT(lhs);
				}
				return FormulaT(rhs);
			case carl::Relation::NEQ:
				// var >= lhs_value && var != rhs_value
				// lhs_value = rhs_value -> var > lhs_value
				// lhs_value < rhs_value -> no simplifications
				// lhs_value > rhs_value -> var >= lhs_value
				if (comparison_result == carl::Relation::EQ) {
					return FormulaT(VariableComparisonT(lhs.var(), lhs_value, carl::Relation::GREATER, false));
				}
				if (comparison_result == carl::Relation::LESS) {
					return std::nullopt;
				}
				return FormulaT(lhs);
			}
		} else if (lhs_relation == carl::Relation::NEQ) {
			switch (rhs_relation) {
			case carl::Relation::LESS:
			case carl::Relation::LEQ:
			case carl::Relation::EQ:
			case carl::Relation::GREATER:
			case carl::Relation::GEQ:
				// handled symmetric cases
				return std::nullopt;
			case carl::Relation::NEQ:
				// var != lhs_value && var != rhs_value
				// lhs_value = rhs_value -> var != lhs_value
				// otherwise -> no simplifications
				if (comparison_result == carl::Relation::EQ) {
					return FormulaT(lhs);
				}
				return std::nullopt;
			}
		}
		return std::nullopt; // unreachable
	}
	if (parent_relation == carl::FormulaType::OR) {
		if (lhs_relation == carl::Relation::LESS) {
			switch (rhs_relation) {
			case carl::Relation::LESS:
				// var < lhs_value || var < rhs_value
				// lhs_value >= rhs_value -> var < lhs_value
				// lhs_value < rhs_value -> var < rhs_value
				if (comparison_result == carl::Relation::GREATER || comparison_result == carl::Relation::EQ) {
					return FormulaT(lhs);
				}
				return FormulaT(rhs);
			case carl::Relation::LEQ:
				// var < lhs_value || var <= rhs_value
				// lhs_value <= rhs_value -> var <= rhs_value
				// lhs_value > rhs_value -> var < lhs_value
				if (comparison_result == carl::Relation::LESS || comparison_result == carl::Relation::EQ) {
					return FormulaT(rhs);
				}
				return FormulaT(lhs);
			case carl::Relation::EQ:
				// var < lhs_value || var = rhs_value
				// lhs_value = rhs_value -> var <= lhs_value
				// lhs_value > rhs_value -> var < lhs_value
				// lhs_value < rhs_value -> no simplifications
				if (comparison_result == carl::Relation::EQ) {
					return FormulaT(VariableComparisonT(lhs.var(), lhs_value, carl::Relation::LEQ, false));
				}
				if (comparison_result == carl::Relation::GREATER) {
					return FormulaT(lhs);
				}
				return std::nullopt;
			case carl::Relation::GREATER:
				// var < lhs_value || var > rhs_value
				// lhs_value = rhs_value -> var != lhs_value
				// lhs_value > rhs_value -> true
				// lhs_value < rhs_value -> no simplifications
				if (comparison_result == carl::Relation::EQ) {
					return FormulaT(VariableComparisonT(lhs.var(), lhs_value, carl::Relation::NEQ, false));
				}
				if (comparison_result == carl::Relation::GREATER) {
					return FormulaT(carl::FormulaType::TRUE);
				}
				return std::nullopt;
			case carl::Relation::GEQ:
				// var < lhs_value || var >= rhs_value
				// lhs_value >= rhs_value -> true
				// lhs_value < rhs_value -> no simplifications
				if (comparison_result == carl::Relation::LESS || comparison_result == carl::Relation::EQ) {
					return FormulaT(carl::FormulaType::TRUE);
				}
				return std::nullopt;
			case carl::Relation::NEQ:
				// var < lhs_value || var != rhs_value
				// lhs_value <= rhs_value -> var != rhs_value
				// lhs_value > rhs_value -> true
				if (comparison_result == carl::Relation::LESS || comparison_result == carl::Relation::EQ) {
					return FormulaT(VariableComparisonT(lhs.var(), rhs_value, carl::Relation::NEQ, false));
				}
				return FormulaT(carl::FormulaType::TRUE);
			}
		} else if (lhs_relation == carl::Relation::LEQ) {
			switch (rhs_relation) {
			case carl::Relation::LESS:
				// handled symmetric case
				return std::nullopt;
			case carl::Relation::LEQ:
				// var <= lhs_value || var <= rhs_value
				// lhs_value >= rhs_value -> var <= lhs_value
				// lhs_value < rhs_value -> var <= rhs_value
				if (comparison_result == carl::Relation::GREATER || comparison_result == carl::Relation::EQ) {
					return FormulaT(lhs);
				}
				return FormulaT(rhs);
			case carl::Relation::EQ:
				// var <= lhs_value || var = rhs_value
				// lhs_value >= rhs_value -> var <= lhs_value
				// lhs_value < rhs_value -> no simplifications
				if (comparison_result == carl::Relation::GREATER || comparison_result == carl::Relation::EQ) {
					return FormulaT(lhs);
				}
				return std::nullopt;
			case carl::Relation::GREATER:
				// var <= lhs_value || var > rhs_value
				// lhs_value >= rhs_value -> true
				// lhs_value < rhs_value -> no simplifications
				if (comparison_result == carl::Relation::GREATER || comparison_result == carl::Relation::EQ) {
					return FormulaT(carl::FormulaType::TRUE);
				}
				return std::nullopt;
			case carl::Relation::GEQ:
				// var <= lhs_value || var >= rhs_value
				// lhs_value >= rhs_value -> true
				// lhs_value < rhs_value -> no simplifications
				if (comparison_result == carl::Relation::GREATER || comparison_result == carl::Relation::EQ) {
					return FormulaT(carl::FormulaType::TRUE);
				}
				return std::nullopt;
			case carl::Relation::NEQ:
				// var <= lhs_value || var != rhs_value
				// lhs_value >= rhs_value -> true
				// lhs_value < rhs_value -> var != rhs_value
				if (comparison_result == carl::Relation::GREATER || comparison_result == carl::Relation::EQ) {
					return FormulaT(carl::FormulaType::TRUE);
				}
				return FormulaT(VariableComparisonT(lhs.var(), rhs_value, carl::Relation::NEQ, false));
			}
		} else if (lhs_relation == carl::Relation::EQ) {
			switch (rhs_relation) {
			case carl::Relation::LESS:
			case carl::Relation::LEQ:
				// handled symmetric cases
				return std::nullopt;
			case carl::Relation::EQ:
				// var = lhs_value || var = rhs_value
				// lhs_value = rhs_value -> var = lhs_value
				// otherwise no simplifications
				if (comparison_result == carl::Relation::EQ) {
					return FormulaT(lhs);
				}
				return std::nullopt;
			case carl::Relation::GREATER:
				// var = lhs_value || var > rhs_value
				// lhs_value = rhs_value -> var >= lhs_value
				// lhs_value > rhs_value -> var > rhs_value
				// lhs_value < rhs_value -> no simplifications
				if (comparison_result == carl::Relation::EQ) {
					return FormulaT(VariableComparisonT(lhs.var(), lhs_value, carl::Relation::GEQ, false));
				}
				if (comparison_result == carl::Relation::GREATER) {
					return FormulaT(rhs);
				}
				return std::nullopt;
			case carl::Relation::GEQ:
				// var = lhs_value || var >= rhs_value
				// lhs_value >= rhs_value -> x >= rhs_value
				// lhs_value < rhs_value -> no simplifications
				if (comparison_result == carl::Relation::GREATER || comparison_result == carl::Relation::EQ) {
					return FormulaT(rhs);
				}
				return std::nullopt;
			case carl::Relation::NEQ:
				// var = lhs_value || var != rhs_value
				// lhs_value = rhs_value -> true
				// lhs_value <> rhs_value -> var != rhs_value
				if (comparison_result == carl::Relation::EQ) {
					return FormulaT(carl::FormulaType::TRUE);
				}
				return FormulaT(VariableComparisonT(lhs.var(), rhs_value, carl::Relation::NEQ, false));
			}
		} else if (lhs_relation == carl::Relation::GREATER) {
			switch (rhs_relation) {
			case carl::Relation::LESS:
			case carl::Relation::LEQ:
			case carl::Relation::EQ:
				// handled symmetric cases
				return std::nullopt;
			case carl::Relation::GREATER:
				// var > lhs_value || var > rhs_value
				// lhs_value <= rhs_value -> var > lhs_value
				// lhs_value > rhs_value -> var > rhs_value
				if (comparison_result == carl::Relation::LESS || comparison_result == carl::Relation::EQ) {
					return FormulaT(lhs);
				}
				return FormulaT(rhs);
			case carl::Relation::GEQ:
				// var > lhs_value || var >= rhs_value
				//  lhs_value >= rhs_value -> var >= rhs_value
				//  lhs_value < rhs_value -> var > lhs_value
				if (comparison_result == carl::Relation::GREATER || comparison_result == carl::Relation::EQ) {
					return FormulaT(rhs);
				}
				return FormulaT(lhs);
			case carl::Relation::NEQ:
				// var > lhs_value || var != rhs_value
				// lhs_value >= rhs_value -> var != rhs_value
				// lhs_value < rhs_value -> true
				if (comparison_result == carl::Relation::GREATER || comparison_result == carl::Relation::EQ) {
					return FormulaT(rhs);
				}
				return FormulaT(carl::FormulaType::TRUE);
			}
		} else if (lhs_relation == carl::Relation::GEQ) {
			switch (rhs_relation) {
			case carl::Relation::LESS:
			case carl::Relation::LEQ:
			case carl::Relation::EQ:
			case carl::Relation::GREATER:
				// handled symmetric cases
				return std::nullopt;
			case carl::Relation::GEQ:
				// var >= lhs_value || var >= rhs_value
				// lhs_value <= rhs_value -> var >= lhs_value
				// lhs_value > rhs_value -> var >= rhs_value
				if (comparison_result == carl::Relation::LESS || comparison_result == carl::Relation::EQ) {
					return FormulaT(lhs);
				}
				return FormulaT(rhs);
			case carl::Relation::NEQ:
				// var >= lhs_value || var != rhs_value
				// lhs_value <= rhs_value -> true
				// lhs_value > rhs_value -> var != rhs_value
				if (comparison_result == carl::Relation::LESS || comparison_result == carl::Relation::EQ) {
					return FormulaT(carl::FormulaType::TRUE);
				}
				return FormulaT(rhs);
			}
		} else if (lhs_relation == carl::Relation::NEQ) {
			switch (rhs_relation) {
			case carl::Relation::LESS:
			case carl::Relation::LEQ:
			case carl::Relation::EQ:
			case carl::Relation::GREATER:
			case carl::Relation::GEQ:
				// handled symmetric cases
				return std::nullopt;
			case carl::Relation::NEQ:
				// var != lhs_value || var != rhs_value
				// lhs_value = rhs_value -> var != lhs_value
				// otherwise -> true
				if (comparison_result == carl::Relation::EQ) {
					return FormulaT(lhs);
				}
				return FormulaT(carl::FormulaType::TRUE);
			}
		}
		return std::nullopt; // unreachable
	}
	return std::nullopt; // unreachable
}

inline std::optional<FormulaT> simplifyVariableComparison(const FormulaT& lhs_formula, const FormulaT& rhs_formula, const carl::FormulaType& parent_relation) {
	std::optional<VariableComparisonT> lhs;
	std::optional<VariableComparisonT> rhs;
	if (lhs_formula.type() == carl::FormulaType::VARCOMPARE) {
		lhs = lhs_formula.variable_comparison();
	} else {
		lhs = convertToVarCompareIfPossible(lhs_formula);
		if (!lhs) {
			return std::nullopt;
		}
		SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Converted: " << lhs_formula << " to " << lhs.value())
	}
	if (rhs_formula.type() == carl::FormulaType::VARCOMPARE) {
		rhs = rhs_formula.variable_comparison();
	} else {
		rhs = convertToVarCompareIfPossible(rhs_formula);
		if (!rhs) {
			return std::nullopt;
		}
		SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Converted: " << rhs_formula << " to " << rhs.value())
	}

	if (lhs.value().var() != lhs.value().var()) {
		// different variables -> no simplification possible
		SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Not comparable")
		return std::nullopt;
	}
	// compared variables are equal, values are equal -> simplifications based on relations
	return simplifyRelationVariableComparison(parent_relation, lhs.value(), rhs.value());
}

class VariableComparisonSimplification : public FormulaTransformer<std::pair<FormulaT, bool>> {

	std::pair<FormulaT, bool> handle_and_or(const FormulaNode& node) {
		assert(node.getChildren().size() >= 2);
		SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Handling AND/OR: " << node)
		auto formula_type = node.getType();
		SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Formula Type: " << formula_type)
		for (const auto& child : node.getChildren()) {
			SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Child Results: " << child.hash() << " -> " << getResult(child))
		}
		// Iterate over the variable comparisons and simplify
		std::set<FormulaT> resulting_simplifications;
		std::unordered_set<FormulaNode> used_in_simplifications;
		bool change = false;
		for (const auto& outer : node.getChildren()) {
			if (used_in_simplifications.contains(outer)) {
				continue;
			}
			for (const auto& inner : node.getChildren()) {
				if (used_in_simplifications.contains(inner) || outer == inner) {
					continue;
				}
				auto& [outer_formula, outer_change] = getResult(outer);
				auto& [inner_formula, inner_change] = getResult(inner);
				change = change || outer_change || inner_change;
				auto current_simplification = simplifyVariableComparison(outer_formula, inner_formula, formula_type);
				if (current_simplification.has_value()) {
					SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Simplification: " << current_simplification.value());
					resulting_simplifications.insert(current_simplification.value());
					used_in_simplifications.insert(outer);
					used_in_simplifications.insert(inner);
					SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Used in simplifications: " << outer_formula << " and " << inner_formula)
					change = true; // simplification was possible
					break;
				} else {
					SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "No simplification possible");
				}
			}
		}

		// Build simplified Formula:
		std::vector<FormulaT> subformulas;
		for (const auto& child : node.getChildren()) {
			if (used_in_simplifications.find(child) == used_in_simplifications.end()) {
				auto& [child_formula, child_change] = getResult(child);
				SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "" << child_formula << " not used in any simplifications")
				subformulas.push_back(child_formula);
				change = change || child_change;
			}
		}
		for (const auto& child : resulting_simplifications) {
			SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Adding simplification " << child)
			subformulas.push_back(child);
		}
		if (subformulas.size() == 1) {
			return std::make_pair(subformulas[0], true);
		}
		FormulaT result = FormulaT(formula_type, subformulas);
		SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Resulting Subformulas: " << subformulas);
		SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Result: " << result);
		return std::make_pair(result, change);
	}

public:
	explicit VariableComparisonSimplification(const FormulaT& formula)
		: FormulaTransformer(formula) {
		SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "VariableComparisonSimplification: " << formula);
		registerHandler({carl::FormulaType::FALSE, carl::FormulaType::TRUE, carl::FormulaType::CONSTRAINT, carl::FormulaType::VARCOMPARE}, [](const auto& node) { return std::make_pair(node.getFormula(), false); });
		registerHandler({carl::FormulaType::AND, carl::FormulaType::OR}, [this](const auto& node) { return handle_and_or(node); });
	}
};

} // namespace smtrat::qe::coverings