#pragma once

#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>
#include <carl-arith/ran/ran.h>
#include <carl-arith/poly/libpoly/LPPolynomial.h>

namespace smtrat::cadcells {


using VariableOrdering = std::vector<carl::Variable>;

#ifdef USE_LIBPOLY
using Polynomial = carl::LPPolynomial;
#else 
using Polynomial = carl::ContextPolynomial<Rational>;
#endif
using Constraint = carl::BasicConstraint<Polynomial>;
using MultivariateRoot = carl::MultivariateRoot<Polynomial>;
using VariableComparison = carl::VariableComparison<Polynomial>;
using Atom = std::variant<Constraint, VariableComparison>;
using Disjunction = std::vector<Atom>;
using CNF = std::vector<Disjunction>;
using RAN = Polynomial::RootType;
using Assignment = carl::Assignment<RAN>;

static const Assignment empty_assignment;

}

