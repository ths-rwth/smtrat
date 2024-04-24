#pragma once

#include "../../smtrat-mcsat.h"

#include "AAFStatistics.h"

namespace smtrat {
namespace mcsat {
namespace arithmetic {

struct AssignmentFinder {

#ifdef SMTRAT_DEVOPTION_Statistics
	AAFStatistics& mStatistics = statistics_get<AAFStatistics>("mcsat-assignment-arithmetic");
#endif

	#ifdef USE_LIBPOLY
	using Polynomial = carl::LPPolynomial;
	#else 
	using Polynomial = carl::ContextPolynomial<Rational>;
	#endif

	mutable std::map<FormulaT,carl::BasicConstraint<Polynomial>> m_cache_constraints;
	mutable std::map<FormulaT,carl::VariableComparison<Polynomial>> m_cache_varcomp;

	std::optional<AssignmentOrConflict> operator()(const mcsat::Bookkeeping& data, carl::Variable var) const;
	bool active(const mcsat::Bookkeeping& data, const FormulaT& f) const;
};

}
}
}
