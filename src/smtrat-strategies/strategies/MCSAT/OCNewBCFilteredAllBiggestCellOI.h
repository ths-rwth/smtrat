#pragma once

#include <smtrat-solver/Manager.h>

// #include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/SATModule/SATModule.tpp>


namespace smtrat {

namespace internal {
struct OCSettings : smtrat::mcsat::onecell::BaseSettings {
	constexpr static bool exploit_strict_constraints = false;

	constexpr static auto cell_heuristic = cadcells::representation::BIGGEST_CELL_FILTER_ONLY_INDEPENDENT;
    constexpr static auto covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_FILTER_ONLY_INDEPENDENT;
	constexpr static auto op = cadcells::operators::op::mccallum_filtered_all_biggest_cell;
};

struct SATSettings : smtrat::SATSettingsMCSAT {
	struct MCSATSettings : mcsat::Base {
		using AssignmentFinderBackend = mcsat::arithmetic::AssignmentFinder;
		using ExplanationBackend = mcsat::SequentialExplanation<mcsat::onecell::Explanation<OCSettings>, mcsat::nlsat::Explanation>;
	};
};
} // namespace internal

class MCSAT_OCNewBCFilteredAllBiggestCellOI : public Manager {
public:
	MCSAT_OCNewBCFilteredAllBiggestCellOI()
		: Manager() {
		setStrategy(
			addBackend<SATModule<internal::SATSettings>>());
	}
};

} // namespace smtrat
