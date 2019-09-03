#pragma once

#include <smtrat-common/smtrat-common.h>
#include <carl-model/evaluation/ModelEvaluation.h>
#include <smtrat-solver/Module.h>

namespace smtrat {

enum class MaxSMTStrategy { FU_MALIK_INCREMENTAL, MSU3, LINEAR_SEARCH };
inline std::ostream& operator<<(std::ostream& os, MaxSMTStrategy ucs) {
	switch (ucs) {
		case MaxSMTStrategy::FU_MALIK_INCREMENTAL: return os << "FU_MALIK_INCREMENTAL";
		case MaxSMTStrategy::MSU3: return os << "MSU3";
		case MaxSMTStrategy::LINEAR_SEARCH: return os << "LINEAR_SEARCH";
	}
}

namespace maxsmt {

std::vector<FormulaT> satisfiedFormulas(const std::vector<FormulaT>& formulas, const Model& model) {
	std::vector<FormulaT> result;
	for (const auto& f : formulas) {
		auto res = carl::model::substitute(FormulaT(f), model);
		if (res.isTrue()) {
			result.push_back(f);
		}
	}
	return result;
}

template<typename Solver>
ModuleInput::iterator addToSolver(Solver& solver, const FormulaT& formula)
{
	solver.add(formula);
	for (auto it = solver.formulaBegin(); it != solver.formulaEnd(); ++it) {
		if (it->formula() == formula) {
			return it;
		}
	}
	assert(false && "Formula was not added correctly to backend. Expected to find formula.");
	return solver.formulaEnd();
}

template<typename Solver, MaxSMTStrategy Strategy>
struct MaxSMTBackend {};


template<typename Solver, MaxSMTStrategy Strategy>
class MaxSMT {
private:
	Solver mSolver;
	std::vector<FormulaT> mSoftFormulas; // TODO add support for weights

public:
	MaxSMT(const Solver& s) {
		for (const auto& form: s.formula()) {
			mSolver.add(form.formula());
		}
	}

	void addSoftFormula(const FormulaT& formula) {
		mSoftFormulas.push_back(formula);
	}

	const std::vector<FormulaT>& softFormulas() const {
		return mSoftFormulas;
	}

	const bool active() const {
		return !mSoftFormulas.empty();
	}

	std::pair<Answer,Model> computeMax() {
		SMTRAT_LOG_INFO("smtrat.maxsmt", "Running MAXSMT.");
		Answer ans = mSolver.check();
		SMTRAT_LOG_DEBUG("smtrat.maxsmt", "Checking satisfiability of hard clauses -> " << ans);
		if (ans != Answer::SAT) return std::make_pair(ans, Model());
		SMTRAT_LOG_INFO("smtrat.maxsmt", "Maximize weight for soft formulas " << mSoftFormulas);
		MaxSMTBackend<Solver,Strategy>().run(mSolver, mSoftFormulas);
		SMTRAT_LOG_DEBUG("smtrat.maxsmt", "Maximal set of satisfied soft clauses " << satisfiedFormulas(softFormulas(), mSolver.model()));
		return std::make_pair(Answer::SAT, mSolver.model());
	}
};



}
}
