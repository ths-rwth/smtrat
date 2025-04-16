#pragma once

#include <smtrat-solver/Manager.h>


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

	struct OpSettings : cadcells::operators::MccallumUnifiedSettingsComplete {
		static constexpr DelineationFunction delineation_function = ALL;
		static constexpr bool only_rational_samples = true;
	};
	using op = cadcells::operators::MccallumUnified<OpSettings>;
};

struct SATSettings : smtrat::SATSettingsMCSAT {
	struct MCSATSettings : mcsat::Base {
		using ExplanationBackend = mcsat::onecell::Explanation<OCSettings>;
	};
	using VarScheduler = VarSchedulerMcsatTheoryFirstBooleanMoreFirst<TheoryVarSchedulerStatic<mcsat::VariableOrdering::FeatureBasedPickering>,true>;
};
} // namespace internal

class Eval_McsatPBcldrat : public Manager {
public:
	Eval_McsatPBcldrat() : Manager() {
		setStrategy(
			
				addBackend<SATModule<internal::SATSettings>>()
			
		);
	}
};

} // namespace smtrat
