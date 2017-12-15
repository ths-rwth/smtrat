#pragma once

#include "../common.h"
#include "../Bookkeeping.h"
#include "ExplanationGenerator.h"

namespace smtrat {
namespace mcsat {
namespace nlsat {

struct Explanation {
	FormulaT operator()(const mcsat::Bookkeeping& data, carl::Variable var, const FormulasT& reason, const FormulaT& implication) const {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Explaining " << implication << " by " << reason);
		std::vector<carl::Variable> orderedVars(data.orderedVariables().begin(), data.orderedVariables().end());
		orderedVars.push_back(var);
		std::reverse(orderedVars.begin(), orderedVars.end());
		
		ExplanationGenerator eg(reason, orderedVars, data.model());
		return eg.getExplanation(implication);
	}
};

}
}
}
