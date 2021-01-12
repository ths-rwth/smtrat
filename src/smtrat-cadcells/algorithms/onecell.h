#pragma once

#include <set>
#include "../datastructures/varorder.h"

#include "../datastructures/polynomials.h"

namespace smtrat::cadcells::algorithms {

void onecell(const std::set<Poly>& polynomials, const datastructures::variable_ordering& vars, const assignment& sample);

}
