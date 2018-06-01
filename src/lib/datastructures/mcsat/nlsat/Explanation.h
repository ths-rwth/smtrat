#pragma once

#include "../common.h"
#include "../Bookkeeping.h"
#include "ExplanationGenerator.h"

#include "NLSATStatistics.h"

namespace smtrat {
namespace mcsat {
namespace nlsat {

struct Explanation {
	
#ifdef SMTRAT_DEVOPTION_Statistics
	mutable NLSATStatistics mStatistics;
#endif
  /**
   * We construct a formula 'E -> I', i.e. 'e1 &  e2 ... en -> i', called "Explanation",
   * in its clausal form '-e1 v -e2 ... en v i',
   * where e1, e2.. are @p reason Atoms and CAD cell bound atoms, and i is the @p implication.
   * It "explains" why the assignment point in @p data is inconsistent with the
   * @p reason atoms/constraints and the implication in that it constructs a whole region
   * of assignments points, which the assignment point in @p data is a part of.
   *
   * @param variableOrdering Determine the order of variables, e.g. x1, x2, .. x10
   * @param data Represent the assigned variables and their assigned values in different representations.
   * These are a prefix of the @p variableOrdering, e.g. x1, x2, .. x5
   * @param var The smallest/first variable in the @p variableOrdering that is not assigned by @p data, e.g. x6
   * @param reason A collection of atoms that are inconsistent together or imply the @p implication.
   * These atoms mention only variables x1, x2.. x6 (some atom definitely mentions x6) and possibly
   * x7..x10 if they are irrelevant and "vanish" under the assignment in @p data,
   * e.g. x1*x7+x6=0 (for x1 := 0) or x6*(x7^2+1)>0 (equiv to x6>0, since x7^2+1 > 0)
   * @param implication A single atom like in @p reason, or False.
   * @return
   */
	boost::optional<FormulaT> operator()(const mcsat::Bookkeeping& data, const std::vector<carl::Variable>& variableOrdering, carl::Variable var, const FormulasT& reason, const FormulaT& implication) const {
#ifdef SMTRAT_DEVOPTION_Statistics
		mStatistics.explanation();
#endif
		SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "With " << reason << " explain " << implication);

		// 'variableOrder' is ordered 'x0,.., xk, .., xn', the relevant variables that appear in the
		// reason and implication end at 'var'=xk, so the relevant prefix is 'x0 ... xk'
		// where CAD would start its variable elimination from back ('xk') to front ('x0').
		// However, the CAD implementation starts eliminating at the front:
		std::vector<carl::Variable> orderedVars(variableOrdering);
		std::reverse(orderedVars.begin(), orderedVars.end());
		SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Ascending variable order " << variableOrdering << " and eliminating down from " << var);

		SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Bookkeep: " << data);
		ExplanationGenerator eg(reason, orderedVars, var, data.model());
		return eg.getExplanation(implication);
	}
};

}
}
}
