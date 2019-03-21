#pragma once

#include "UnsatCore.h"
#include "UnsatCore_ModelExclusion.h"

#include <smtrat-common/smtrat-common.h>

namespace smtrat {

template<typename Solver>
FormulasT computeUnsatCore(const Solver& solver, UnsatCoreStrategy strategy) {
	SMTRAT_LOG_INFO("smtrat.unsatcore", "Computing UNSAT core.");
	switch (strategy) {
		case UnsatCoreStrategy::Counting:
		case UnsatCoreStrategy::ModelExclusion:
			return unsatcore::UnsatCore<Solver, UnsatCoreStrategy::ModelExclusion>(solver).computeCore();
	}
	SMTRAT_LOG_WARN("smtrat.unsatcore", "Unsat core computation failed as unknown strategy " << strategy << " was selected.");
	return FormulasT();
}

}