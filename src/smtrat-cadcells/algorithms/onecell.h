#pragma once

#include <set>
#include "../common.h"

namespace smtrat::cadcells::algorithms {

std::optional<std::pair<FormulasT, FormulaT>> onecell(const FormulasT& constraints, const VariableOrdering& vars, const Assignment& sample);

}
