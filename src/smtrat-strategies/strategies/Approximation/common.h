#pragma once

#include <smtrat-modules/SATModule/SATModule.h>

namespace apx = smtrat::cadcells::representation::approximation;

namespace smtrat::strategies::approximation {

struct OpSettings : cadcells::operators::MccallumFilteredSettings {
	static constexpr DelineationFunction delineation_function = COMPOUND_PWL;
};

struct BaseOCSettings : smtrat::mcsat::onecell::BaseSettings {
	constexpr static bool exploit_strict_constraints = true;
    constexpr static bool use_approximation          = true;

	using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellFilter;
	using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringFilter;
	using op = cadcells::operators::MccallumFiltered<OpSettings>;
};

template<typename OCSettings>
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

}