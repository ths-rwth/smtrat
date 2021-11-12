#pragma once

#include <set>
#include "../common.h"

namespace smtrat::cadcells::algorithms {

/**
 * An MCAST-style single cell explanation function.
 * 
 * A set of constraints is called infeasible w.r.t. an assignment if the defining polynomials are univariate under the sample and there does not exists a value for the unassigned variable that satisfies all constraints.
 * 
 * This method eliminates the unassigned variable using @ref get_level_covering or @ref get_delineation and then constructs a single cell in the assigned variables level by level.
 * 
 * @param constraints Atoms of the same level such that @ref sample cannot be extended for the highest variable without making one atom false. Note that this property is not checked.
 * @param sample A sample such that all but the highest variable in @ref constraints are assigned.
 * @return A pair of a set of constraints causign the conflict and a formula describing the cell.
 */
std::optional<std::pair<FormulasT, FormulaT>> onecell(const FormulasT& constraints, const VariableOrdering& vars, const Assignment& sample);

}
