#pragma once

#include <smtrat-common/smtrat-common.h>
#include <carl-model/Model.h>
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

/// Contains strategy implementations for max SMT computations.
namespace maxsmt {

template<typename Solver, MaxSMTStrategy Strategy>
class MaxSMTBackend {};

}


template<typename Solver, MaxSMTStrategy Strategy>
class MaxSMT {
private:
	Solver& mSolver;
	std::vector<FormulaT> mSoftFormulas;
	std::map<FormulaT, std::string> mSoftFormulaIds;

	bool satisfied(const FormulaT& formula, const Model& model) {
		return carl::model::substitute(formula, model).isTrue();
	}

public:
	MaxSMT(Solver& s) : mSolver(s) {}

	void add_soft_formula(const FormulaT& formula, Rational weight, const std::string& id) {
		// TODO add support for weights
		if (weight != 1) {
			SMTRAT_LOG_WARN("smtrat.maxsmt", "Weights are not yet supported by MaxSMT backends.");
		}
		mSoftFormulas.push_back(formula);
		mSoftFormulaIds.emplace(formula, id);
	}

	void remove_soft_formula(const FormulaT& formula) {
		mSoftFormulas.erase(std::remove(mSoftFormulas.begin(), mSoftFormulas.end(), formula));
		mSoftFormulaIds.erase(formula);
	}

	void reset() {
		mSoftFormulas.clear();
	}

	const bool active() const {
		return !mSoftFormulas.empty();
	}

	std::tuple<Answer,Model,ObjectiveValues> compute() {
		SMTRAT_LOG_INFO("smtrat.maxsmt", "Running MAXSMT.");
		Answer ans = mSolver.check();
		SMTRAT_LOG_DEBUG("smtrat.maxsmt", "Checking satisfiability of hard clauses -> " << ans);
		if (ans != Answer::SAT) return std::make_tuple(ans, Model(), ObjectiveValues());
		SMTRAT_LOG_INFO("smtrat.maxsmt", "Maximize weight for soft formulas " << mSoftFormulas);
		mSolver.push();
		ans = maxsmt::MaxSMTBackend<Solver,Strategy>(mSolver, mSoftFormulas).run();
		mSolver.pop();
		if (!is_sat(ans)) {
			SMTRAT_LOG_INFO("smtrat.maxsmt", "Got unexpected response " << ans);
			return std::make_tuple(ans, Model(), ObjectiveValues());
		} else {
			std::map<std::string, Rational> objectives;
			for (const auto& f : mSoftFormulas) {
				if (satisfied(f, mSolver.model())) {
					SMTRAT_LOG_DEBUG("smtrat.maxsmt", "Satisfied soft clause " << f << " of weight 1 with id " << mSoftFormulaIds.at(f));
					objectives[mSoftFormulaIds.at(f)] += 1; // weights should be resprected here
				} else {
					objectives[mSoftFormulaIds.at(f)];
				}
			}
			ObjectiveValues results;
			for (const auto& p : objectives) results.emplace_back(p);
			return std::make_tuple(Answer::SAT, mSolver.model(), results);
		}
	}
};

}
