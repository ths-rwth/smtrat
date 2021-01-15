#pragma once

#include <set>
#include "../common.h"

namespace smtrat::cadcells::algorithms {

void onecell(const std::set<Poly>& polynomials, const variable_ordering& vars, const assignment& sample);

}
