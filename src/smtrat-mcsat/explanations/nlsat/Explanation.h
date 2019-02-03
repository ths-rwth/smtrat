#pragma once

#include "NLSATStatistics.h"

#include <smtrat-common/smtrat-common.h>
#include <smtrat-mcsat/smtrat-mcsat.h>

namespace smtrat {
namespace mcsat {
namespace nlsat {

struct Explanation {

#ifdef SMTRAT_DEVOPTION_Statistics
	mutable NLSATStatistics mStatistics;
	Explanation()
		: mStatistics("mcsat-explanation-nlsat") {}
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
	 */
	boost::optional<mcsat::Explanation> operator()(const mcsat::Bookkeeping& data, carl::Variable var, const FormulasT& reason) const;
};

} // namespace nlsat
} // namespace mcsat
} // namespace smtrat
