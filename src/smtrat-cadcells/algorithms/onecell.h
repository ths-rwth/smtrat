#pragma once

#include <set>
#include "../common.h"

namespace smtrat::cadcells::algorithms {

std::optional<FormulaT> onecell(const FormulasT& constraints, const variable_ordering& vars, const assignment& sample);

}
