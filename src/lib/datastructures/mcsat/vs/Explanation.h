#pragma once

#include "../common.h"
#include "ExplanationGenerator.h"

#include "VSStatistics.h"

#include <smtrat-mcsat/smtrat-mcsat.h>

namespace smtrat {
namespace mcsat {
namespace vs {

struct Explanation {

#ifdef SMTRAT_DEVOPTION_Statistics
	mutable VSStatistics mStatistics;
    Explanation() : mStatistics("mcsat-explanation-vs") {}
#endif

	boost::optional<mcsat::Explanation> operator()(const mcsat::Bookkeeping& data, const std::vector<carl::Variable>& variableOrdering, carl::Variable var, const FormulasT& reason) const {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Explain conflict " << reason );
		#ifdef SMTRAT_DEVOPTION_Statistics
		mStatistics.explanationCalled();
		#endif
		// 'variableOrder' is ordered 'x0,.., xk, .., xn', the relevant variables that appear in the
		// reason and implication end at 'var'=xk, so the relevant prefix is 'x0 ... xk'
		// where VS starts its variable elimination from back ('xk') to front ('x0').
		SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Ascending variable order " << variableOrdering << " and eliminating down from " << var);
		SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Bookkeep: " << data);
		ExplanationGenerator<DefaultSettings> eg(reason, variableOrdering, var, data.model());
		auto ret = eg.getExplanation();
		if (ret == boost::none) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Could not generate explanation");
		}
		#ifdef SMTRAT_DEVOPTION_Statistics
		mStatistics.explanationSuccess();
		#endif
		return ret;
	}
};

}
}
}
