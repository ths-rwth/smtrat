#include "Explanation.h"

#include "ExplanationGenerator.h"

#include "NLSATStatistics.h"

namespace smtrat {
namespace mcsat {
namespace nlsat {

boost::optional<mcsat::Explanation> Explanation::operator()(const mcsat::Bookkeeping& data, carl::Variable var, const FormulasT& reason) const {
#ifdef SMTRAT_DEVOPTION_Statistics
	mStatistics.explanationCalled();
#endif
	SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Explain conflict " << reason);

	// compute compatible complete variable ordering
	std::vector variableOrdering(data.assignedVariables());
	for (const auto& v : data.variables()) {
		if (std::find(data.assignedVariables().begin(), data.assignedVariables().end(), v) == data.assignedVariables().end()) {
			variableOrdering.push_back(v);
		}
	}

	// 'variableOrder' is ordered 'x0,.., xk, .., xn', the relevant variables that appear in the
	// reason and implication end at 'var'=xk, so the relevant prefix is 'x0 ... xk'
	// where CAD would start its variable elimination from back ('xk') to front ('x0').
	// However, the CAD implementation starts eliminating at the front:
	std::vector<carl::Variable> orderedVars(variableOrdering);
	std::reverse(orderedVars.begin(), orderedVars.end());
	SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Ascending variable order " << variableOrdering << " and eliminating down from " << var);

	SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Bookkeep: " << data);
	ExplanationGenerator eg(reason, orderedVars, var, data.model());
#ifdef SMTRAT_DEVOPTION_Statistics
	mStatistics.explanationSuccess();
#endif
	return eg.getExplanation(FormulaT(carl::FormulaType::FALSE));
}

}
}
}
