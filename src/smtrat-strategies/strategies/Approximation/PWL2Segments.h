#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/SATModule/SATModule.tpp>

#include "common.h"

namespace smtrat {

namespace internal {

struct PWLSettings {
    using Sampling = apx::SampleSimple;
    static constexpr double pwl_fallback_distance = 1.0;
    static constexpr std::size_t pwl_num_segments = 2;
    using PWLBuilder = apx::AdvancedPWLBuilder;
    static constexpr bool refine_pwl = false;
};

struct ApxSettings {
    using method = apx::PiecewiseLinear<PWLSettings>;
    using Criteria = apx::Criteria<typename apx::BaseCriteriaSettings>;
};

struct OCSettings : smtrat::strategies::approximation::BaseOCSettings {
    using Criteria = ApxSettings::Criteria;
	using cell_apx_heuristic = cadcells::representation::cell_heuristics::BiggestCellApproximation<ApxSettings>;
};

struct SATSettings : smtrat::SATSettingsMCSAT {
	struct MCSATSettings : mcsat::Base {
		using AssignmentFinderBackend = mcsat::arithmetic::AssignmentFinder;
		using ExplanationBackend = mcsat::SequentialExplanation<mcsat::onecell::Explanation<OCSettings>,
                                                                mcsat::nlsat::Explanation>;
	};
};

} // namespace internal

class Approximation_PWL2Segments : public Manager {
public:
	Approximation_PWL2Segments()
		: Manager() {
		setStrategy(
			addBackend<SATModule<internal::SATSettings>>());
	}
};

} // namespace smtrat