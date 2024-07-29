#pragma once

#include <smtrat-solver/Manager.h>

// #include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/SATModule/SATModule.tpp>


namespace smtrat {

namespace internal {
struct OpSettings : cadcells::operators::MccallumFilteredSettings {
	static constexpr DelineationFunction delineation_function = ALL;
	static constexpr bool only_irreducible_resultants = true;
	static constexpr bool only_rational_samples = true;
};

struct OCSettings : smtrat::mcsat::onecell::BaseSettings {
	constexpr static bool exploit_strict_constraints = false;

	constexpr static auto cell_heuristic = cadcells::representation::BIGGEST_CELL_FILTER_ONLY_INDEPENDENT;
    constexpr static auto covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_FILTER_ONLY_INDEPENDENT;
	using op = cadcells::operators::MccallumFiltered<OpSettings>;
};

struct SATSettings : smtrat::SATSettingsMCSAT {
	struct MCSATSettings : mcsat::Base {
		using AssignmentFinderBackend = mcsat::arithmetic::AssignmentFinder;
		using ExplanationBackend = mcsat::SequentialExplanation<mcsat::onecell::Explanation<OCSettings>, mcsat::nlsat::Explanation>;
	};
};
} // namespace internal

class Filter_BCIrredIndepRational : public Manager {
public:
	Filter_BCIrredIndepRational()
		: Manager() {
		setStrategy(
			addBackend<SATModule<internal::SATSettings>>());
	}
};

} // namespace smtrat
