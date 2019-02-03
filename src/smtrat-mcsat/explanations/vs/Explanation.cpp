#include "Explanation.h"

#include "ExplanationGenerator.h"

namespace smtrat {
namespace mcsat {
namespace vs {

boost::optional<mcsat::Explanation> Explanation::operator()(const mcsat::Bookkeeping& data, carl::Variable var, const FormulasT& reason) const {
	SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Explain conflict " << reason);
	#ifdef SMTRAT_DEVOPTION_Statistics
	mStatistics.explanationCalled();
	#endif
	// 'variableOrder' is ordered 'x0,.., xk, .., xn', the relevant variables that appear in the
	// reason and implication end at 'var'=xk, so the relevant prefix is 'x0 ... xk'
	// where VS starts its variable elimination from back ('xk') to front ('x0').
	std::vector varOrder(data.assignedVariables());
	varOrder.push_back(var);
	SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Ascending variable order " << varOrder << " and eliminating down from " << var);
	SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Bookkeep: " << data);
	ExplanationGenerator<DefaultSettings> eg(reason, varOrder, var, data.model());
	auto ret = eg.getExplanation();
	if (ret == boost::none) {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Could not generate explanation");
	}
	#ifdef SMTRAT_DEVOPTION_Statistics
	mStatistics.explanationSuccess();
	#endif
	return ret;
}

}
}
}