#pragma once

#include <smtrat-solver/Manager.h>

// #include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/SATModule/SATModule.tpp>


namespace smtrat {

namespace internal {
struct OCSettings : smtrat::mcsat::onecell::BaseSettings {
	constexpr static bool exploit_strict_constraints = false;

	using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCell;
	using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCovering;

	using op = cadcells::operators::Mccallum<cadcells::operators::MccallumSettingsComplete>;
};

struct SATSettings : smtrat::SATSettingsMCSAT {
	struct MCSATSettings : mcsat::Base {
		using ExplanationBackend = mcsat::onecell::Explanation<OCSettings>;
	};
};
} // namespace internal

class MCSAT_OCNewBC : public Manager {
public:
	MCSAT_OCNewBC() : Manager() {
		setStrategy(addBackend<SATModule<internal::SATSettings>>());
	}
};

} // namespace smtrat
