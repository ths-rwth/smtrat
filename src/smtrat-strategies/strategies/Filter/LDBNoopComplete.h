#pragma once

#include <smtrat-solver/Manager.h>

// #include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/SATModule/SATModule.tpp>


namespace smtrat {

namespace internal {
struct OCSettings : smtrat::mcsat::onecell::BaseSettings {
	constexpr static bool exploit_strict_constraints = false;

	using cell_heuristic = cadcells::representation::cell_heuristics::LowestDegreeBarriersFilter;
    using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringFilter;
	using op = cadcells::operators::MccallumFiltered<cadcells::operators::MccallumFilteredCompleteSettings>;
};

struct SATSettings : smtrat::SATSettingsMCSAT {
	struct MCSATSettings : mcsat::Base {
		using AssignmentFinderBackend = mcsat::arithmetic::AssignmentFinder;
		using ExplanationBackend = mcsat::SequentialExplanation<mcsat::onecell::Explanation<OCSettings>>;
	};
};
} // namespace internal

class Filter_LDBNoop : public Manager {
public:
	Filter_LDBNoop()
		: Manager() {
		setStrategy(
			addBackend<SATModule<internal::SATSettings>>());
	}
};

} // namespace smtrat
