#pragma once

#include "../common.h"
#include "../Bookkeeping.h"
#include "ExplanationGenerator.h"

namespace smtrat {
namespace mcsat {
namespace vs {

struct Explanation {
	boost::optional<FormulaT> operator()(const mcsat::Bookkeeping& data, const std::vector<carl::Variable>& variableOrdering, carl::Variable var, const FormulasT& reason, const FormulaT& implication) const {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "With " << reason << " explain " << implication);

		std::cout << "**EXPLAIN CALL**" << std::endl; // TODO remove, for debugging

		// 'variableOrder' is ordered 'x0,.., xk, .., xn', the relevant variables that appear in the
		// reason and implication end at 'var'=xk, so the relevant prefix is 'x0 ... xk'
		// where VS starts its variable elimination from back ('xk') to front ('x0').
		SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Ascending variable order " << variableOrdering << " and eliminating down from " << var);
		SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Bookkeep: " << data);
		ExplanationGenerator eg(reason, variableOrdering, var, data.model());
		auto ret = eg.getExplanation(implication);

		// TODO remove, for debugging:
		try {
			std::cout << "**" << ret.value() << "**" << std::endl;
		}
		catch (const boost::bad_optional_access&) {
			std::cout << "**INCOMPLETE**" << std::endl;
		}
		
		return ret;
	}
};

}
}
}
