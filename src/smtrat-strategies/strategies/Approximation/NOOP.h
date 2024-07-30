#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/SATModule/SATModule.tpp>

#include "common.h"

namespace smtrat {

namespace internal {

struct OpSettings : cadcells::operators::MccallumFilteredSettings {
	static constexpr DelineationFunction delineation_function = COMPOUND_PWL;
};

struct OCSettings : smtrat::strategies::approximation::BaseOCSettings {
    constexpr static bool use_approximation          = false;
};

struct SATSettings : smtrat::SATSettingsMCSAT {
	struct MCSATSettings : mcsat::Base {
		using AssignmentFinderBackend = mcsat::arithmetic::AssignmentFinder;
		using ExplanationBackend = mcsat::SequentialExplanation<mcsat::onecell::Explanation<OCSettings>,
                                                                mcsat::nlsat::Explanation>;
	};
};
} // namespace internal

class Approximation_Noop : public Manager {
public:
	Approximation_Noop()
		: Manager() {
		setStrategy(
			addBackend<SATModule<internal::SATSettings>>());
	}
};

} // namespace smtrat
