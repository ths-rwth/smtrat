#pragma once

#include <smtrat-common/types.h>
#include <smtrat-coveringng/types.h>

namespace smtrat::qe::coverings::util {

FormulaT to_formula(const cadcells::datastructures::PolyPool& pool, carl::Variable variable, const cadcells::datastructures::SymbolicInterval& interval);

FormulaT to_formula_true_only(const cadcells::datastructures::PolyPool& pool, const covering_ng::ParameterTree& tree);

FormulaT to_formula_alternate(const cadcells::datastructures::PolyPool& pool, const covering_ng::ParameterTree& tree);

} // namespace smtrat::qe::coverings