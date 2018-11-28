#pragma once

#include "feature_based.h"
#include "greedy_max_univariate.h"

namespace smtrat {
namespace mcsat {

enum class VariableOrdering {
	GreedyMaxUnivariate,
	FeatureBased
};

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
	}
}

}
}
