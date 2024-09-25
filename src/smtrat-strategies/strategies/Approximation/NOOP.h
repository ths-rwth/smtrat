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

struct SATSettings : smtrat::SATSettingsMCSAT {
	struct MCSATSettings : mcsat::Base {
		using AssignmentFinderBackend = mcsat::arithmetic::AssignmentFinder;
		using ExplanationBackend = mcsat::SequentialExplanation<
                                       mcsat::fm::Explanation<mcsat::fm::DefaultSettings>,
									   mcsat::icp::Explanation,
									   mcsat::vs::Explanation,
									   mcsat::onecell::Explanation<OCSettings>,
									   mcsat::onecell::Explanation<mcsat::onecell::DefaultSettings>
                                    >;
	};
};
} // namespace internal

class Approximation_Noop : public Manager {
public:
	Approximation_Noop() : Manager() {
        setStrategy(
            addBackend<FPPModule<FPPSettings1>>({
                addBackend<STropModule<STropSettings3>>({
                    addBackend<SATModule<internal::SATSettings>>()
                })
            })
        );
	}
};

} // namespace smtrat
