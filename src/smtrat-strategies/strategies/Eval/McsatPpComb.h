#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/SATModule/SATModule.tpp>
#include <smtrat-cadcells/operators/operator_mccallum_unified.h>


namespace smtrat {

namespace internal {
struct OCSettings : smtrat::mcsat::onecell::BaseSettings {
	constexpr static bool exploit_strict_constraints = false;
	static constexpr bool enforce_tarski = false;
    constexpr static bool use_approximation = false;
	using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellFilter;
	using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringFilter;
	using op = cadcells::operators::MccallumUnified<cadcells::operators::MccallumUnifiedSettingsComplete>;
};

struct SATSettings : smtrat::SATSettingsMCSAT {
	struct MCSATSettings : mcsat::Base {
		using ExplanationBackend = mcsat::SequentialExplanation<mcsat::fm::Explanation<mcsat::fm::DefaultSettings>,mcsat::icp::Explanation,mcsat::vs::Explanation,mcsat::onecell::Explanation<OCSettings>>;
	};
	using VarScheduler = VarSchedulerMinisat;
};
} // namespace internal

class Eval_McsatPpComb : public Manager {
public:
	Eval_McsatPpComb() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
				addBackend<SATModule<internal::SATSettings>>()
			})
		);
	}
};

} // namespace smtrat
