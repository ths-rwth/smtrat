#pragma once

#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>
#include <carl/ran/ran.h>

namespace smtrat::cadcells {

using RAN = carl::real_algebraic_number<Rational>;
using Assignment = carl::ran_assignment<Rational>;
using VariableOrdering = std::vector<carl::Variable>;

static const Assignment empty_assignment;

}

