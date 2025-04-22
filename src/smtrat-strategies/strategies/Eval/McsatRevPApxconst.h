#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/SATModule/SATModule.tpp>
#include <smtrat-cadcells/operators/operator_mccallum_unified.h>

namespace smtrat {

namespace internal {

namespace apx = smtrat::cadcells::representation::approximation;

struct ApxSettings {
    using method = apx::Simple<apx::SimpleSettings>;
    struct CriteriaSettings : apx::BaseCriteriaSettings {
        static constexpr std::size_t approximated_cells_limit = 100;
        static constexpr std::size_t single_degree_threshold  = 3;
        static constexpr std::size_t dynamic_degree_scale     = 2;
    };
    using Criteria = apx::Criteria<CriteriaSettings>;
};

struct OCSettings : smtrat::mcsat::onecell::BaseSettings {
    constexpr static bool exploit_strict_constraints = false;
	static constexpr bool enforce_tarski = false;
    constexpr static bool use_approximation = true;
	using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellFilter;
	using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringFilter;
	using op = cadcells::operators::MccallumUnified<cadcells::operators::MccallumUnifiedSettingsComplete>;

    using Criteria = ApxSettings::Criteria;
	using cell_apx_heuristic = cadcells::representation::cell_heuristics::BiggestCellApproximation<ApxSettings>;
};

struct SATSettings : smtrat::SATSettingsMCSAT {
	struct MCSATSettings : mcsat::Base {
		using ExplanationBackend = mcsat::onecell::Explanation<OCSettings>;
	};
	using VarScheduler = VarSchedulerMcsatTheoryFirstBooleanMoreFirst<TheoryVarSchedulerStatic<mcsat::VariableOrdering::FeatureBasedPickeringReverse>,true>;
};

} // namespace internal

class Eval_McsatRevPApxconst : public Manager {
public:
    Eval_McsatRevPApxconst() : Manager() {
        setStrategy(
            addBackend<SATModule<internal::SATSettings>>()
        );
	}
};

} // namespace smtrat
