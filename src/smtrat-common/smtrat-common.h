#pragma once

#include "config.h"
#include "logging.h"

#include "settings/Settings.h"

#include <carl/core/MultivariatePolynomial.h>
#include <carl/core/Variable.h>
#include <carl/core/VariableInformation.h>
#include <carl/formula/Formula.h>
#include <carl/formula/Logic.h>
#include <carl/io/streamingOperators.h>
#include <carl/util/enum_util.h>

#include <atomic>

namespace smtrat {

using carl::operator<<;

using Conditionals = std::vector<std::atomic_bool*>;

using Rational = mpq_class;

using Integer = carl::IntegralType<Rational>::type;

using TermT = carl::Term<Rational>;

using Poly = carl::MultivariatePolynomial<Rational>;

using Factorization = std::map<Poly, carl::uint>;

using ConstraintT = carl::Constraint<Poly>;

using ConstraintsT = carl::Constraints<Poly>;

using VariableAssignmentT = carl::VariableAssignment<Poly>;	

using VariableComparisonT = carl::VariableComparison<Poly>;

using FormulaT = carl::Formula<Poly>;

using FormulasT = carl::Formulas<Poly>;

using FormulaSetT = carl::FormulaSet<Poly>;

using FormulasMultiT = std::multiset<FormulaT>;

using EvalRationalMap = std::map<carl::Variable, Rational>;

using VarPolyInfo = carl::VariableInformation<true, Poly>;

// Pair of priority and module id (within the respective strategy graph)
using thread_priority = std::pair<std::size_t, std::size_t>;

// An enum with the levels for lemma generation
enum LemmaLevel { NONE = 0, NORMAL = 1, ADVANCED = 2 };


///An enum with the possible answers a Module can give
enum Answer { SAT = 0, UNSAT = 1, UNKNOWN = 2, ABORTED = 3, OPTIMAL = 4 };
inline bool is_sat(Answer a) { return a == SAT || a == OPTIMAL; }
inline std::ostream& operator<<(std::ostream& os, Answer a) {
	switch (a) {
		case Answer::SAT:		return os << "SAT";
		case Answer::UNSAT:		return os << "UNSAT";
		case Answer::UNKNOWN:	return os << "UNKNOWN";
		case Answer::ABORTED:	return os << "ABORTED";
		case Answer::OPTIMAL:	return os << "OPTIMAL";
		default:
			assert(false && "Invalid enum value for Answer");
			return os << "Answer(" << carl::underlying_enum_value(a) << ")";
	}
}

}

#ifdef EXTERNALIZE_CLASSES
namespace carl {

extern template class MultivariatePolynomial<smtrat::Rational>;
extern template class Constraint<smtrat::Poly>;
extern template class Formula<smtrat::Poly>;

}
#endif
