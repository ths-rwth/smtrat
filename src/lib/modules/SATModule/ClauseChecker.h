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
		SMTRAT_LOG_DEBUG("smtrat.sat", "Model: " << model);
		for (const auto& f: formulas) {
			ModelValue res = carl::model::evaluate(f, model);
			SMTRAT_LOG_DEBUG("smtrat.sat", f << " -> " << res);
			if (res.isBool()) {
				allFalse = allFalse && !res.asBool();
			} else return;
		}
		if (allFalse) std::quick_exit(66);
		assert(!allFalse);
	}
	template<typename TT>
	void operator()(const Minisat::Clause& c, const TT& bcm) const {
		FormulasT f;
		for (int i = 0; i < c.size(); i++) {
			auto v = var(c[i]);
			// Check wether this literal is a constraint abstraction
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

template<typename T, typename TT>
void validateClause(const T& t, const TT& tt, bool enabled) {
	if (enabled) ClauseChecker()(t, tt);
}

}
}
}
