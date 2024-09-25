#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/SATModule/SATModule.tpp>
#include <smtrat-modules/STropModule/STropModule.h>

#include "common.h"

namespace smtrat {

namespace internal {

struct TaylorSettings {
	static constexpr std::size_t taylor_deg = 1;
	using Sampling = apx::SampleSimple;
};

struct ApxSettings {
    using method = apx::Taylor<TaylorSettings>;
    using Criteria = apx::Criteria<typename apx::BaseCriteriaSettings>;
};

struct OCSettings : smtrat::strategies::approximation::BaseOCSettings {
    using Criteria = ApxSettings::Criteria;
	using cell_apx_heuristic = cadcells::representation::cell_heuristics::BiggestCellApproximation<ApxSettings>;
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

class Approximation_Taylor : public Manager {
public:
	Approximation_Taylor() : Manager() {
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
