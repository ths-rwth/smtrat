#pragma once

#include <algorithm>
#include <variant>
#include <vector>

#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/types.h>
#include <carl-arith/core/Variable.h>
#include <carl-arith/ran/Conversion.h>
#include <smtrat-cadcells/operators/operator.h>
#include <smtrat-coveringng/Algorithm_NuCAD.h>

#include "Settings.h"
#include "smtrat-cadcells/datastructures/roots.h"
#include "smtrat-coveringng/VariableOrdering.h"

namespace smtrat::qe::nucad {

using Settings = DefaultSettings;

std::optional<FormulaT> qe(const FormulaT& formula);

} // namespace smtrat::qe::nucad
