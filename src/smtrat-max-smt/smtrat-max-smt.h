#pragma once

#include "MaxSMT.h"
#include "MaxSMT_LinearSearch.h"
#include "MaxSMT_MSU3.h"
#include "MaxSMT_FuMalikIncremental.h"

#include <smtrat-common/smtrat-common.h>

namespace smtrat {

template<MaxSMTStrategy Strategy, typename Solver>
auto computeMaxSMT(const Solver& solver) {
	SMTRAT_LOG_INFO("smtrat.unsatcore", "Computing MaxSMT.");
	auto handler = maxsmt::MaxSMT<Solver, Strategy>(solver);
	for (auto softFormula : solver.weightedFormulas()) {
		handler.addSoftFormula(softFormula.first);
	}
	return handler.computeMax();
}

}