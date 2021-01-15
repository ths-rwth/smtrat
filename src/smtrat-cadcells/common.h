#pragma once

#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>
#include <carl/ran/ran.h>

namespace smtrat::cadcells {

using ran = carl::real_algebraic_number<Rational>;
using assignment = carl::ran_assignment<Rational>;
using variable_ordering = std::vector<carl::Variable>;

}

