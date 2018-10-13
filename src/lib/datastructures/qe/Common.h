#pragma once

#include "../../Common.h"

namespace smtrat{
namespace qe{
  using Variable = carl::Variable;
  using Variables = std::vector<Variable>;

  using Rational = mpq_class;
  using Polynomial = carl::MultivariatePolynomial<Rational>;
  using Polynomials = std::vector<Polynomial>;

  using Constraint = carl::Constraint<Polynomial>;
  using Constraints = std::vector<Constraint>;

  using Formula = carl::Formula<Polynomial>;
  using Formulas = std::vector<Formula>;

  using RAN = carl::RealAlgebraicNumber<Rational>;
  using Assignment = std::map<Variable, RAN>;
}
}
