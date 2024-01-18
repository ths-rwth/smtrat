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

FormulaT to_formula(const cadcells::datastructures::PolyPool& pool, carl::Variable variable, const cadcells::datastructures::SymbolicInterval& interval) {
	auto dnf = cadcells::helper::to_formula(pool, variable, interval);
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
	return FormulaT(carl::FormulaType::AND, std::move(result));
}

FormulaT to_formula_true_only(const cadcells::datastructures::PolyPool& pool, const covering_ng::ParameterTree& tree) {
	if (!tree.status) {
		return FormulaT(carl::FormulaType::FALSE);
	}
	assert(tree.status || boost::indeterminate(tree.status));

	FormulaT children_formula(carl::FormulaType::TRUE);
	if (boost::indeterminate(tree.status)) {
		FormulasT children_formulas;
		for (const auto& child : tree.children) {
			children_formulas.push_back(to_formula_true_only(pool, child));
		}
		children_formula = FormulaT(carl::FormulaType::OR, std::move(children_formulas));
	}
		
	FormulaT interval_formula(carl::FormulaType::TRUE);
	if (tree.interval) {
		interval_formula = to_formula(pool, *tree.variable, *tree.interval);
	}

	return FormulaT(carl::FormulaType::AND, { interval_formula, children_formula });
}

template<typename Pol>
auto count_arithmetic_constraints(const carl::Formula<Pol>& f) {
	std::size_t counter;
    carl::visit(f,
        [&counter](const carl::Formula<Pol>& f) {
			if (f.type() == carl::FormulaType::CONSTRAINT) counter++;
        }
    );
	return counter;
}

FormulaT to_formula_alternate_helper(const cadcells::datastructures::PolyPool& pool, const covering_ng::ParameterTree& tree, bool inverse) {
	if ((!inverse && !tree.status) || (inverse && tree.status)) {
		return FormulaT(carl::FormulaType::FALSE);
	}
	assert(((!inverse && tree.status) || (inverse && !tree.status)) || boost::indeterminate(tree.status));

	FormulaT children_formula(carl::FormulaType::TRUE);
	if (boost::indeterminate(tree.status)) {
		FormulasT children_formulas;
		for (const auto& child : tree.children) {
			auto res_pos = to_formula_alternate_helper(pool, child, inverse);
			auto res_neg = to_formula_alternate_helper(pool, child, !inverse);
			if (count_arithmetic_constraints(res_pos) <= count_arithmetic_constraints(res_neg)) {
				children_formulas.push_back(res_pos);
			} else {
				children_formulas.push_back(res_neg.negated());
			}
		}
		children_formula = FormulaT(carl::FormulaType::OR, std::move(children_formulas));
	}
		
	FormulaT interval_formula(carl::FormulaType::TRUE);
	if (tree.interval) {
		interval_formula = to_formula(pool, *tree.variable, *tree.interval);
	}

	return FormulaT(carl::FormulaType::AND, { interval_formula, children_formula });
}

FormulaT to_formula_alternate(const cadcells::datastructures::PolyPool& pool, const covering_ng::ParameterTree& tree) {
	auto res_pos = to_formula_alternate_helper(pool, tree, false);
	auto res_neg = to_formula_alternate_helper(pool, tree, true);
	if (count_arithmetic_constraints(res_pos) <= count_arithmetic_constraints(res_neg)) {
		return res_pos;
	} else {
		return res_neg.negated();
	}
}

} // namespace smtrat::qe::coverings