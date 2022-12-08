#pragma once

#include <iostream>
#include <smtrat-common/smtrat-common.h>

namespace smtrat {

enum class UnsatCoreStrategy { /* Counting, */ ModelExclusion };
inline std::ostream& operator<<(std::ostream& os, UnsatCoreStrategy ucs) {
	switch (ucs) {
		// case UnsatCoreStrategy::Counting: return os << "Counting";
		case UnsatCoreStrategy::ModelExclusion: return os << "ModelExclusion";
	}
}

/// Contains strategy implementations for unsat core computations.
namespace unsatcore {

template<typename Solver, UnsatCoreStrategy Strategy>
class UnsatCoreBackend {};

}


template<typename Solver, UnsatCoreStrategy Strategy>
class UnsatCore {
private:
	std::map<FormulaT, std::string> mAnnotatedNames;
	std::vector<FormulaT> mFormulas;
	Solver& mSolver;

public:
	UnsatCore(Solver& s) : mSolver(s) {}

	void add_annotated_name(const FormulaT& formula, const std::string& name) {
		mAnnotatedNames.emplace(formula, name);
		mFormulas.emplace_back(formula);
	}

	void remove_annotated_name(const FormulaT& formula) {
		mAnnotatedNames.erase(formula);
		mFormulas.erase(std::find(mFormulas.begin(), mFormulas.end(), formula));
	}

	void reset() {
		mAnnotatedNames.clear();
	}

	bool active() const {
		return mAnnotatedNames.empty();
	}

	std::pair<Answer,FormulasT> compute_core(const FormulasT& formulas) {
		// we assume that mSolver is UNSAT
		if (false) {
			// check satisfiability
			Answer ans = mSolver.check();
			SMTRAT_LOG_DEBUG("smtrat.unsatcore", "Checking satisfiability -> " << ans);
			if (is_sat(ans))
				return std::make_pair(Answer::SAT, FormulasT());
		}

		for (const auto& f : formulas) {
			mSolver.remove(f);
		}

		SMTRAT_LOG_INFO("smtrat.unsatcore", "Calculate unsat core for " << formulas);
		mSolver.push();
		auto result = unsatcore::UnsatCoreBackend<Solver,Strategy>(mSolver, formulas).run();
		mSolver.pop();

		for (const auto& f : formulas) {
			mSolver.add(f);
		}

		return result;
	}

	std::pair<Answer,std::vector<std::string>> compute() {
		SMTRAT_LOG_INFO("smtrat.unsatcore", "Running unsat cores using named formulas " << mAnnotatedNames);
		auto result = compute_core(mFormulas);
		if (result.first == Answer::UNSAT) {
			SMTRAT_LOG_DEBUG("smtrat.unsatcore", "Got unsat core " << result.second);
			std::vector<std::string> core;
			for (const auto& f : result.second) {
				assert(mAnnotatedNames.find(f) != mAnnotatedNames.end());
				core.push_back(mAnnotatedNames[f]);
			}
			return std::make_pair(Answer::UNSAT, core);
		} else {
			return std::make_pair(result.first, std::vector<std::string>());
		}
	}
};

}
