#pragma once

#include "config.h"
#include "CompileInfo.h"
#include "logging.h"

#include <carl/core/MultivariatePolynomial.h>
#include <carl/core/Variable.h>
#include <carl/formula/Formula.h>
#include <carl/io/streamingOperators.h>
#include <carl/util/enum_util.h>

namespace smtrat {

using carl::operator<<;

using Rational = mpq_class;

using Poly = carl::MultivariatePolynomial<Rational>;

using ConstraintT = carl::Constraint<Poly>;

using ConstraintsT = carl::Constraints<Poly>;

using FormulaT = carl::Formula<Poly>;

using FormulasT = carl::Formulas<Poly>;

using FormulaSetT = carl::FormulaSet<Poly>;


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