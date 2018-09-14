#pragma once

#include "../../modules/SATModule/SATModule.h"
#include "../../solver/Manager.h"

namespace smtrat {
enum class UnsatCoreStrategy { Counting, ModelExclusion };

/// Contains helper for unsat core computations.
namespace unsatcore {
template<typename Solver, UnsatCoreStrategy Strategy>
class UnsatCore {};

template<typename Solver>
class UnsatCore<Solver, UnsatCoreStrategy::Counting> {};

/**
 * Separates the input formula into two parts: labeled and unlabeled ones.
 * This follows @cite SMTLIB26 (4.2.7)
 */
template<typename Solver>
bool separateFormulas(const Solver* solver, FormulasT& unlabeled, std::map<std::string,FormulasT>& labeled) {
	FormulaSetT input;
	std::map<FormulaT,std::string> labels;
	
	for (const auto& f: *solver) input.insert(f.formula());
	for (const auto& nf: solver->namedFormulas()) {
		if (nf.second.getType() == carl::FormulaType::AND) {
			for (const auto& f: nf.second.subFormulas()) {
				if (labels.find(f) != labels.end()) {
					SMTRAT_LOG_ERROR("smtrat.unsatcore", "Unable to separate formula as formula appeared twice: " << f);
					return false;
				}
				labels.emplace(nf.second, f);
			}
		} else {
			if (labels.find(nf.second) != labels.end()) {
				SMTRAT_LOG_ERROR("smtrat.unsatcore", "Unable to separate formula as formula appeared twice: " << nf.second);
				return false;
			}
			labels.emplace(nf.second, nf.first);
		}
	}
	
	unlabeled.clear();
	labeled.clear();
	for (const auto& i: input) {
		auto it = labels.find(i);
		if (it == labels.end()) {
			unlabeled.emplace_back(i);
		} else {
			labeled[it->second].emplace_back(i);
		}
	}
	return true;
}

}

template<typename Solver>
FormulasT computeUnsatCore(const Solver* solver, UnsatCoreStrategy strategy) {
	switch (strategy) {
		case UnsatCoreStrategy::Counting:
		case UnsatCoreStrategy::ModelExclusion:
			return unsatcore::UnsatCore<Solver, UnsatCoreStrategy::ModelExclusion>(solver).computeCore();
	}
}

}

#include "UnsatCore_ModelExclusion.h"
