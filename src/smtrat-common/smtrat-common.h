#pragma once

#include "config.h"
#include "CompileInfo.h"
#include "logging.h"

#include "RuntimeSettings.h"
#include "ValidationSettings.h"

#include "settings/Settings.h"

#include <carl/core/MultivariatePolynomial.h>
#include <carl/core/Variable.h>
#include <carl/core/VariableInformation.h>
#include <carl/formula/Formula.h>
#include <carl/io/streamingOperators.h>
#include <carl/util/enum_util.h>

namespace smtrat {

using carl::operator<<;

using Rational = mpq_class;

using Integer = carl::IntegralType<Rational>::type;

using TermT = carl::Term<Rational>;

using Poly = carl::MultivariatePolynomial<Rational>;

using Factorization = std::map<Poly, carl::uint>;

using ConstraintT = carl::Constraint<Poly>;

using ConstraintsT = carl::Constraints<Poly>;

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
enum Answer { SAT = 0, UNSAT = 1, UNKNOWN = 2, ABORTED = 3 };
inline std::ostream& operator<<(std::ostream& os, Answer a) {
	switch (a) {
		case Answer::SAT:		return os << "SAT";
		case Answer::UNSAT:		return os << "UNSAT";
		case Answer::UNKNOWN:	return os << "UNKNOWN";
		case Answer::ABORTED:	return os << "ABORTED";
		default:
			assert(false && "Invalid enum value for Answer");
			return os << "Answer(" << carl::underlying_enum_value(a) << ")";
	}
}

}