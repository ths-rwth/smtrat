#include "Explanation.h"

#include "../common.h"
#include "ExplanationGenerator.h"

#include "NLSATStatistics.h"

namespace smtrat {
namespace mcsat {
namespace nlsat {

boost::optional<mcsat::Explanation> Explanation::operator()(const mcsat::Bookkeeping& data, const std::vector<carl::Variable>& variableOrdering, carl::Variable var, const FormulasT& reason) const {
#ifdef SMTRAT_DEVOPTION_Statistics
	mStatistics.explanation();
#endif
	SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Explain conflict " << reason);

	// 'variableOrder' is ordered 'x0,.., xk, .., xn', the relevant variables that appear in the
	// reason and implication end at 'var'=xk, so the relevant prefix is 'x0 ... xk'
	// where CAD would start its variable elimination from back ('xk') to front ('x0').
	// However, the CAD implementation starts eliminating at the front:
	std::vector<carl::Variable> orderedVars(variableOrdering);
	std::reverse(orderedVars.begin(), orderedVars.end());
	SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Ascending variable order " << variableOrdering << " and eliminating down from " << var);

	SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Bookkeep: " << data);
	ExplanationGenerator eg(reason, orderedVars, var, data.model());
	return eg.getExplanation(FormulaT(carl::FormulaType::FALSE));
}

}
}
}
