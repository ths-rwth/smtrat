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
#include <carl-formula/formula/functions/NNF.h>
#include "../../coverings/util/to_formula.h"

namespace smtrat::qe::nucad::util {

std::pair<FormulaT,std::vector<carl::Variable>> to_formula_true_only_elim_redundant_internal(const cadcells::datastructures::PolyPool& pool, const covering_ng::ParameterTree& tree) {
	if (tree.status == 0) {
		return std::make_pair(FormulaT(carl::FormulaType::FALSE), std::vector<carl::Variable>());
	}
	assert(tree.status > 0);

	std::vector<carl::Variable> res;
    bool first = true;

	FormulaT children_formula(carl::FormulaType::TRUE);
	if (tree.status == 2) {
		FormulasT children_formulas;
		for (const auto& child : tree.children) {
			auto [formula, subres] = to_formula_true_only_elim_redundant_internal(pool, child);
			children_formulas.push_back(formula);

			if (first) {
				res = subres;
				first = false;
			} else {
				std::vector<carl::Variable> tmp;
				std::set_intersection(res.begin(), res.end(), subres.begin(), subres.end(), std::back_inserter(tmp));
				res = tmp;
			}
		}
		children_formula = FormulaT(carl::FormulaType::OR, std::move(children_formulas));
	}
		
	FormulaT interval_formula(carl::FormulaType::TRUE);
	if (tree.variable) {
		if (std::find(res.begin(),res.end(),*tree.variable) == res.end()) {
			interval_formula = qe::coverings::util::to_formula(pool, *tree.variable, *tree.interval);
            auto it = std::lower_bound(res.begin(), res.end(), *tree.variable);
            res.insert(it, *tree.variable);
        }
	}

	return std::make_pair( FormulaT(carl::FormulaType::AND, { interval_formula, children_formula }), res);
}

FormulaT to_formula_true_only_elim_redundant(const cadcells::datastructures::PolyPool& pool, const covering_ng::ParameterTree& tree) {
	return to_formula_true_only_elim_redundant_internal(pool,tree).first;
}

std::pair<FormulaT,std::vector<carl::Variable>> to_formula_alternate_elim_redundant(const cadcells::datastructures::PolyPool& pool, const covering_ng::ParameterTree& tree, bool positive) {
	std::vector<carl::Variable> res;
    bool first = true;

	FormulaT children_formula(carl::FormulaType::TRUE);
	if (tree.status == 2) {
		auto num_pos = std::count_if(tree.children.begin(), tree.children.end(), [](const auto& child) { return child.status == 1; });
		auto num_neg = std::count_if(tree.children.begin(), tree.children.end(), [](const auto& child) { return child.status == 0; });
		bool encode_positive = (num_pos <= num_neg);
		FormulasT children_formulas;
		for (const auto& child : tree.children) {
			if (child.status == encode_positive || child.status == 2) {
				auto [formula, subres] = to_formula_alternate_elim_redundant(pool, child, encode_positive);
				children_formulas.push_back(formula);

				if (first) {
					res = subres;
					first = false;
				} else {
					std::vector<carl::Variable> tmp;
					std::set_intersection(res.begin(), res.end(), subres.begin(), subres.end(), std::back_inserter(tmp));
					res = tmp;
				}
			}
		}
		children_formula = FormulaT(carl::FormulaType::OR, std::move(children_formulas));
		if ((encode_positive && !positive) || (!encode_positive && positive)) {
			children_formula = carl::to_nnf(children_formula.negated());
			res.clear();
		}
	}
		
	FormulaT interval_formula(carl::FormulaType::TRUE);
	if (tree.variable) {
		if (std::find(res.begin(),res.end(),*tree.variable) == res.end()) {
			interval_formula = qe::coverings::util::to_formula(pool, *tree.variable, *tree.interval);
			auto it = std::lower_bound(res.begin(), res.end(), *tree.variable);
			res.insert(it, *tree.variable);
		}
	}

	return std::make_pair( FormulaT(carl::FormulaType::AND, { interval_formula, children_formula }), res);
}

FormulaT to_formula_alternate_elim_redundant(const cadcells::datastructures::PolyPool& pool, const covering_ng::ParameterTree& tree) {
	if (tree.status == 1) {
		return FormulaT(carl::FormulaType::TRUE);
	} else if (tree.status == 0) {
		return FormulaT(carl::FormulaType::FALSE);
	} else {
		return to_formula_alternate_elim_redundant(pool, tree, true).first;
	}
}

} // namespace smtrat::qe::nucad