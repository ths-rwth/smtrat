#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/SATModule/SATModule.tpp>
#include <smtrat-modules/STropModule/STropModule.h>

#include "common.h"

namespace smtrat {

namespace internal {

struct OCSettings : smtrat::strategies::approximation::BaseOCSettings {
    constexpr static bool use_approximation = false;
};

} // namespace internal

class Approximation_Baseline : public Manager {
public:
	Approximation_Baseline() : Manager() {
        setStrategy(
            addBackend<FPPModule<FPPSettings1>>({
                addBackend<STropModule<STropSettings3>>({
                    addBackend<SATModule<strategies::approximation::SATSettings<internal::OCSettings>>>()
                })
            })
        );
	}
};

} // namespace smtrat
