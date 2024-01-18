#include "to_formula.h"

#include "smtrat-cadcells/datastructures/roots.h"
#include "smtrat-common/types.h"
#include <carl-arith/extended/MultivariateRoot.h>
#include <carl-arith/poly/Conversion.h>
#include <carl-arith/constraint/Conversion.h>
#include <carl-arith/extended/Conversion.h>
#include <smtrat-cadcells/common.h>
#include <smtrat-coveringng/types.h>
#include <smtrat-cadcells/helper_formula.h>

namespace smtrat::qe::coverings::util {

FormulaT to_formula(const cadcells::datastructures::PolyPool& pool, const covering_ng::ParameterTree& tree) {
	if (!tree.status) {
		return FormulaT(carl::FormulaType::FALSE);
	}
	assert(tree.status || boost::indeterminate(tree.status));

	FormulaT children_formula(carl::FormulaType::TRUE);
	if (boost::indeterminate(tree.status)) {
		FormulasT children_formulas;
		for (const auto& child : tree.children) {
			children_formulas.push_back(to_formula(pool, child));
		}
		children_formula = FormulaT(carl::FormulaType::OR, std::move(children_formulas));
	}
		
	FormulaT interval_formula(carl::FormulaType::TRUE);
	if (tree.interval) {
		auto dnf = cadcells::helper::to_formula(pool, *tree.variable, *tree.interval);
		FormulasT result;
		for (const auto& disjunction : dnf) {
			std::vector<FormulaT> tmp;
			for (const auto& f : disjunction) {
				if (std::holds_alternative<cadcells::Constraint>(f)) {
					tmp.push_back(FormulaT(ConstraintT(carl::convert<Poly>(std::get<cadcells::Constraint>(f)))));
				} else if (std::holds_alternative<cadcells::VariableComparison>(f)) {
					auto constraint = carl::as_constraint(std::get<cadcells::VariableComparison>(f));
					if (!constraint) {
						tmp.push_back(FormulaT(carl::convert<Poly>(std::get<cadcells::VariableComparison>(f))));
					} else {
						tmp.push_back(FormulaT(ConstraintT(carl::convert<Poly>(*constraint))));
					}
				} else {
					assert(false);
				}
			}
			result.emplace_back(carl::FormulaType::OR, std::move(tmp));
		}
		interval_formula = FormulaT(carl::FormulaType::AND, std::move(result));
	}

	return FormulaT(carl::FormulaType::AND, { interval_formula, children_formula });
}

} // namespace smtrat::qe::coverings