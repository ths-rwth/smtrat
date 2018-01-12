#pragma once

#include "../common.h"
#include "../Bookkeeping.h"
#include "ExplanationGenerator.h"

namespace smtrat {
namespace mcsat {
namespace nlsat {

struct Explanation {
	FormulaT operator()(const mcsat::Bookkeeping& data, const std::vector<carl::Variable>& variableOrdering, carl::Variable var, const FormulasT& reason, const FormulaT& implication) const {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Explaining " << implication << " by " << reason);
		std::vector<carl::Variable> orderedVars(variableOrdering);
		std::reverse(orderedVars.begin(), orderedVars.end());
		SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Considering variables " << orderedVars << " and eliminating from " << var);
		
		ExplanationGenerator eg(reason, orderedVars, var, data.model());
		return eg.getExplanation(implication);
	}
};

}
}
}
