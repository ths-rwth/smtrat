#pragma once

#include <carl/util/Bitset.h>
#include <carl/util/Covering.h>
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
class UnsatCore<Solver, UnsatCoreStrategy::ModelExclusion> {
private:
	Solver mSolver;
	std::map<carl::Variable, std::pair<FormulaT,std::size_t>> mFormulas;
	std::vector<carl::Bitset> mSets;
	std::size_t mAssignments = 0;
public:
	UnsatCore(const Solver& s) {
		FormulasT phis;
		std::size_t id = 0;
		for (const auto& form: s.formula()) {
			FormulaT f = form.formula();
			auto it = mFormulas.emplace(carl::freshBooleanVariable(), std::make_pair(f, id));
			phis.emplace_back(f.negated());
			mSolver.add(FormulaT(carl::FormulaType::IFF, {FormulaT(it.first->first), f}));
			mSets.emplace_back();
			SMTRAT_LOG_DEBUG("smtrat.unsatcore", it.first->first << " <-> " << f << " with id " << id);
			id++;
		}
		mSolver.add(FormulaT(carl::FormulaType::OR, std::move(phis)));
	}
	void processAssignment() {
		const auto& m = mSolver.model();
		FormulasT subs;
		SMTRAT_LOG_TRACE("smtrat.unsatcore", "Got assignment " << m);
		for (const auto& f: mFormulas) {
			const auto& val = m.evaluated(f.first);
			assert(val.isBool());
			if (val.asBool()) {
				subs.emplace_back(carl::FormulaType::NOT, FormulaT(f.first));
			} else {
				mSets[f.second.second].set(mAssignments, true);
			}
		}
		SMTRAT_LOG_TRACE("smtrat.unsatcore", "Excluding assignment with " << subs);
		mSolver.add(FormulaT(carl::FormulaType::OR, std::move(subs)));
		mAssignments++;
	}
	void compute() {
		while (true) {
			Answer a = mSolver.check();
			switch (a) {
				case Answer::SAT:
					processAssignment();
					break;
				case Answer::UNSAT:
					SMTRAT_LOG_INFO("smtrat.unsatcore", "Formula became unsat.");
					return;
				default:
					SMTRAT_LOG_ERROR("smtrat.unsatcore", "Unexpected answer " << a);
					return;
			}
		}
	}
	FormulasT computeCore() {
		compute();
		carl::Covering<carl::Variable> cover(mSets.size());
		for (const auto& f: mFormulas) {
			SMTRAT_LOG_TRACE("smtrat.unsatcore", "Adding to cover: " << f.first << " -> " << mSets[f.second.second]);
			cover.add(f.first, mSets[f.second.second]);
		}
		assert(cover.conflicts());
		std::vector<carl::Variable> coreVars;
		cover.buildConflictingCore(coreVars);
		FormulasT core;
		for (const auto& v: coreVars) {
			SMTRAT_LOG_DEBUG("smtrat.unsatcore", "In core: " << v << " / " << mFormulas[v].first);
			core.emplace_back(mFormulas[v].first);
		}
		return core;
	}
};

}
}
