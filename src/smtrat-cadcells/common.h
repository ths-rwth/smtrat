#pragma once

#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>
#include <carl-arith/ran/ran.h>

namespace smtrat::cadcells {

using RAN = carl::RealAlgebraicNumber<Rational>;
using Assignment = carl::Assignment<RAN>;
using VariableOrdering = std::vector<carl::Variable>;

using Polynomial = Poly;
using Constraint = carl::BasicConstraint<Poly>;
using MultivariateRoot = carl::MultivariateRoot<Poly>;
using VariableComparison = carl::VariableComparison<Poly>;
using Atom = std::variant<Constraint, VariableComparison>;

static const Assignment empty_assignment;

}

