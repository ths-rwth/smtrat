#pragma once

#include "feature_based.h"
#include "greedy_max_univariate.h"

namespace smtrat {
namespace mcsat {

enum class VariableOrdering {
	GreedyMaxUnivariate,
	FeatureBased,
	FeatureBasedZ3,
	FeatureBasedBrown
};

inline std::string get_name(VariableOrdering ordering) {
	switch (ordering) {
		case VariableOrdering::GreedyMaxUnivariate: return "GreedyMaxUnivariate";
		case VariableOrdering::FeatureBased: return "FeatureBased";
		case VariableOrdering::FeatureBasedZ3: return "FeatureBasedZ3";
		case VariableOrdering::FeatureBasedBrown: return "FeatureBasedBrown";
	}
}

inline std::ostream& operator<<(std::ostream& os, VariableOrdering ordering){
	return os << get_name(ordering);
}

template<VariableOrdering vot, typename Constraints>
std::vector<carl::Variable> calculate_variable_order(const Constraints& c) {
	
	std::vector<ConstraintT> constraints;
	for (int i = 0; i < c.size(); ++i) {
		if (c[i].first == nullptr) continue;
		if (c[i].first->reabstraction.getType() != carl::FormulaType::CONSTRAINT) continue;
		constraints.emplace_back(c[i].first->reabstraction.constraint());
	}
	
	switch (vot) {
		case VariableOrdering::GreedyMaxUnivariate:
			return variableordering::greedy_max_univariate(constraints);
		case VariableOrdering::FeatureBased:
			return variableordering::feature_based(constraints);
		case VariableOrdering::FeatureBasedZ3:
			return variableordering::feature_based_z3(constraints);
		case VariableOrdering::FeatureBasedBrown:
			return variableordering::feature_based_brown(constraints);
	}
}

template<VariableOrdering vot>
std::vector<carl::Variable> calculate_variable_order(const std::vector<ConstraintT>& constraints){

	switch (vot) {
		case VariableOrdering::GreedyMaxUnivariate:
			return variableordering::greedy_max_univariate(constraints);
		case VariableOrdering::FeatureBased:
			return variableordering::feature_based(constraints);
		case VariableOrdering::FeatureBasedZ3:
			return variableordering::feature_based_z3(constraints);
		case VariableOrdering::FeatureBasedBrown:
			return variableordering::feature_based_brown(constraints);
	}
}

}

}

