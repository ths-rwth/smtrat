#pragma once

#include <smtrat-solver/Manager.h>

// #include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/SATModule/SATModule.tpp>


namespace smtrat {

namespace internal {
struct OCSettings : smtrat::mcsat::onecell::BaseSettings {
	constexpr static bool exploit_strict_constraints = false;

	using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellPdel;
	using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringPdel;

	using op = cadcells::operators::MccallumPdel;
};

struct SATSettings : smtrat::SATSettingsMCSAT {
	struct MCSATSettings : mcsat::Base {
		using ExplanationBackend = mcsat::SequentialExplanation<mcsat::onecell::Explanation<OCSettings>,
																mcsat::nlsat::Explanation>;
	};
};
} // namespace internal

class MCSAT_OCNewPdel : public Manager {
public:
	MCSAT_OCNewPdel() : Manager() {
		setStrategy(addBackend<SATModule<internal::SATSettings>>());
	}
};

} // namespace smtrat
