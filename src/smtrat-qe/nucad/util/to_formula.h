#pragma once

#include <smtrat-common/types.h>
#include <smtrat-coveringng/types.h>

namespace smtrat::qe::nucad::util {

FormulaT to_formula_true_only(const cadcells::datastructures::PolyPool& pool, const covering_ng::ParameterTree& tree);

FormulaT to_formula_alternate(const cadcells::datastructures::PolyPool& pool, const covering_ng::ParameterTree& tree);

} // namespace smtrat::qe::coverings