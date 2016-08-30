#pragma once

#include "../../modules/SATModule/SATModule.h"
#include "../../solver/Manager.h"

namespace smtrat {
enum class UnsatCoreStrategy { Counting, ModelExclusion };

namespace unsatcore {
template<typename Solver, UnsatCoreStrategy Strategy>
class UnsatCore {};

template<typename Solver>
class UnsatCore<Solver, UnsatCoreStrategy::Counting> {
private:
public:	
};

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
