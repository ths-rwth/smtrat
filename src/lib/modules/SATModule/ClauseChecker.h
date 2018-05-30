#pragma once

#include "SolverTypes.h"
#include "../../Common.h"

namespace smtrat {
namespace sat {
namespace detail {

struct ClauseChecker {
	Model buildModel() const {
		const auto& vp = carl::VariablePool::getInstance();
		Model model;
		model.emplace(vp.findVariableWithName("X"), Rational(1)/2);
		model.emplace(vp.findVariableWithName("Y"), Rational(-2));
		model.emplace(vp.findVariableWithName("Z"), Rational(2));
		return model;
	}

	void operator()(const FormulaT& formula) const {
		if (formula.getType() == carl::FormulaType::OR) {
			(*this)(formula.subformulas());
		} else {
			(*this)({formula});
		}
	}
	void operator()(const FormulasT& formulas) const {
		auto model = buildModel();
		bool allFalse = true;
		SMTRAT_LOG_DEBUG("smtrat.sat.clausechecker", "Model: " << model);
		for (const auto& f: formulas) {
			ModelValue res = carl::model::evaluate(f, model);
			SMTRAT_LOG_DEBUG("smtrat.sat.clausechecker", f << " -> " << res);
			if (res.isBool()) {
				allFalse = allFalse && !res.asBool();
			} else return;
		}
		//if (allFalse) std::quick_exit(66);
		assert(!allFalse);
	}
	template<typename VM, typename BCM>
	void operator()(const Minisat::Clause& c, const VM& vm, const BCM& bcm) const {
		FormulasT f;
		for (int i = 0; i < c.size(); i++) {
			auto v = var(c[i]);
			// Check whether this literal is a boolean variable
			auto it = vm.find(v);
			if (it != vm.end()) {
				if (sign(c[i])) {
					f.emplace_back(carl::FormulaType::NOT, FormulaT(it->second));
				} else {
					f.emplace_back(it->second);
				}
			}
			// Check whether this literal is a constraint abstraction
			if (v >= bcm.size()) continue;
			if (bcm[v].first == nullptr) continue;
			if (sign(c[i])) {
				f.emplace_back(bcm[v].second->reabstraction);
			} else {
				f.emplace_back(bcm[v].first->reabstraction);
			}
		}
		(*this)(f);
	}
};

template<typename T>
void validateClause(const T& t, bool enabled) {
	if (enabled) ClauseChecker()(t);
}

template<typename T, typename VM, typename BCM>
void validateClause(const T& t, const VM& vm, const BCM& bcm, bool enabled) {
	if (enabled) ClauseChecker()(t, vm, bcm);
}

}
}
}
