#pragma once

#include <smtrat-solver/Manager.h>

// #include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/SATModule/SATModule.tpp>


namespace smtrat {

namespace internal {
struct OpSettings : cadcells::operators::MccallumFilteredSettings {
	static constexpr DelineationFunction delineation_function = BOUNDS_ONLY;
	static constexpr bool only_if_no_intersections = true;
	static constexpr bool enable_weak = true;
};

struct OCSettings : smtrat::mcsat::onecell::BaseSettings {
	constexpr static bool exploit_strict_constraints = false;

	using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellFilter;
    using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringFilter;
	using op = cadcells::operators::MccallumFiltered<OpSettings>;
};

struct SATSettings : smtrat::SATSettingsMCSAT {
	struct MCSATSettings : mcsat::Base {
		using AssignmentFinderBackend = mcsat::arithmetic::AssignmentFinder;
		using ExplanationBackend = mcsat::SequentialExplanation<mcsat::onecell::Explanation<OCSettings>, mcsat::nlsat::Explanation>;
	};
};
} // namespace internal

class Filter_BCBoundsOnlyIntersect : public Manager {
public:
	Filter_BCBoundsOnlyIntersect()
		: Manager() {
		setStrategy(
			addBackend<SATModule<internal::SATSettings>>());
	}
};

} // namespace smtrat
