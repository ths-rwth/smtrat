#pragma once

#include <carl/util/Bitset.h>
#include <carl/util/Covering.h>
#include <carl-covering/carl-covering.h>
#include <smtrat-common/smtrat-common.h>

namespace smtrat {
namespace unsatcore {

/**
 * Implements an easy strategy to obtain an unsatisfiable core.
 * Essentially it computes a cover that rejects all possible models if we allow the removal of clauses.
 *
 * - Allow to disable every formula f_i by encoding (y_i <=> f_i)
 * - Find a satisfying assignment (which will set some f_i to false)
 * - 
 */
template<typename Solver>
class UnsatCoreBackend<Solver, UnsatCoreStrategy::ModelExclusion> {
private:
	Solver& mSolver;
	carl::covering::TypedSetCover<FormulaT> mSetCover;
	std::map<carl::Variable, FormulaT> mFormulas;
	std::size_t mAssignments = 0;
public:
	UnsatCoreBackend<Solver, UnsatCoreStrategy::ModelExclusion>(Solver& s, const FormulasT& fs) : mSolver(s) {
		FormulasT phis;
		std::size_t id = 0;
		for (const auto& f : fs) {
			auto it = mFormulas.emplace(carl::freshBooleanVariable(), f);
			phis.emplace_back(FormulaT(it.first->first));
			mSolver.add(FormulaT(carl::FormulaType::IFF, {FormulaT(it.first->first), f}));
			SMTRAT_LOG_DEBUG("smtrat.unsatcore", it.first->first << " <-> " << f << " with id " << id);
			id++;
		}
		// At least one clause should be active.
		mSolver.add(FormulaT(carl::FormulaType::OR, std::move(phis)));
	}
	void processAssignment() {
		const auto& m = mSolver.model();
		FormulasT subs;
		SMTRAT_LOG_DEBUG("smtrat.unsatcore", "Got assignment " << m);
		for (const auto& f: mFormulas) {
			SMTRAT_LOG_DEBUG("smtrat.unsatcore", "Processing " << f.first);
			const auto& val = m.evaluated(f.first);
			assert(val.isBool());
			if (!val.asBool()) {
				subs.emplace_back(FormulaT(f.first));
				mSetCover.set(f.second, mAssignments);
			}
		}
		SMTRAT_LOG_TRACE("smtrat.unsatcore", "Excluding assignment with " << subs);
		mSolver.add(FormulaT(carl::FormulaType::OR, std::move(subs)));
		mAssignments++;
	}
	Answer compute() {
		while (true) {
			Answer a = mSolver.check();
			switch (a) {
				case Answer::SAT:
					processAssignment();
					break;
				case Answer::UNSAT:
					SMTRAT_LOG_INFO("smtrat.unsatcore", "Formula became unsat.");
					return a;
				case Answer::OPTIMAL:
					assert(false && "solver should not be in optimization mode");
					return a;
				default:
					SMTRAT_LOG_ERROR("smtrat.unsatcore", "Unexpected answer " << a);
					return a;
			}
		}
	}
	std::pair<Answer, FormulasT> run() {
		Answer a = compute();
		if (a != Answer::UNSAT) {
			return std::make_pair(a, FormulasT());
		} else {
			auto covering = mSetCover.get_cover([](auto& sc) {
				carl::Bitset res;
				res |= carl::covering::heuristic::remove_duplicates(sc);
				res |= carl::covering::heuristic::select_essential(sc);
				res |= carl::covering::heuristic::greedy(sc);
				return res;
			});
			SMTRAT_LOG_DEBUG("smtrat.unsatcore", "Greedy: " << covering);
			return std::make_pair(Answer::UNSAT, covering);
		}
	}
};

}
}
