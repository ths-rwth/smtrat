#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/SATModule/SATModule.tpp>
#include <smtrat-modules/STropModule/STropModule.h>

namespace smtrat {

namespace internal {

struct mcf_settings : cadcells::operators::MccallumFilteredSettings {
    static constexpr DelineationFunction delineation_function = NOOP;
};

struct OCSettings : mcsat::onecell::BaseSettings { // current default
    constexpr static bool exploit_strict_constraints = true;

	using cell_heuristic = cadcells::representation::cell_heuristics::LowestDegreeBarriersCacheGlobal;
    using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringFilter;
    using op = cadcells::operators::MccallumFiltered<mcf_settings>;
};

struct SATSettings : SATSettingsMCSAT {
	static constexpr auto moduleName = "SATModule<SATSettingsMCSATAPX>";
    struct MCSATSettings : mcsat::Base {
		using ExplanationBackend = mcsat::SequentialExplanation<mcsat::fm::Explanation<mcsat::fm::DefaultSettings>,
													 			mcsat::icp::Explanation,
													 			mcsat::vs::Explanation,
													 			mcsat::onecell::Explanation<internal::OCSettings>,
													 			mcsat::onecell::Explanation<mcsat::onecell::DefaultSettings>>;

	};
};

}

class MCSAT_PPFMICPVSOCBC: public Manager {
	public:
		MCSAT_PPFMICPVSOCBC(): Manager() {
			setStrategy(
				addBackend<FPPModule<FPPSettings1>>({
					addBackend<STropModule<STropSettings3>>({
						addBackend<SATModule<internal::SATSettings>>()
					})
				})
			);
		}
};

}	// namespace smtrat
