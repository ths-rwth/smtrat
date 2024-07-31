#pragma once

#include <smtrat-solver/Manager.h>

// #include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/SATModule/SATModule.tpp>


namespace smtrat {

namespace internal {
struct OCSettings : smtrat::mcsat::onecell::BaseSettings {
	constexpr static bool exploit_strict_constraints = false;

	using cell_heuristic = cadcells::representation::cell_heuristics::AllCompound;
    using covering_heuristic = cadcells::representation::covering_heuristics::AllCompoundCovering;
	using op = cadcells::operators::Mccallum<cadcells::operators::MccallumSettingsComplete>;
};

struct SATSettings : smtrat::SATSettingsMCSAT {
	struct MCSATSettings : mcsat::Base {
		using ExplanationBackend = mcsat::SequentialExplanation<mcsat::onecell::Explanation<OCSettings>,
																mcsat::nlsat::Explanation>;
	};
};
} // namespace internal

class MCSAT_OCNewCompound : public Manager {
public:
	MCSAT_OCNewCompound() : Manager() {
		setStrategy(addBackend<SATModule<internal::SATSettings>>());
	}
};

} // namespace smtrat
