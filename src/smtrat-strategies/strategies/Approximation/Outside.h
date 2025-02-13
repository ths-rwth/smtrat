#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/SATModule/SATModule.tpp>
#include <smtrat-modules/STropModule/STropModule.h>

#include "common.h"

namespace smtrat {

namespace internal {

struct ApxSettings {
    using method = apx::Simple<apx::SimpleSettings>;
    struct CriteriaSettings : apx::BaseCriteriaSettings {
        static constexpr std::size_t approximated_cells_limit = 50;
        static constexpr std::size_t blocking                 = 0;
        static constexpr std::size_t blocking_increment       = 1;
        static constexpr std::size_t apx_per_constraint_limit = 10;
        static constexpr double      involved_constraint_scale = 10;  
        static constexpr std::size_t single_degree_threshold  = 5;
        static constexpr std::size_t dynamic_degree_scale     = 0;
        static constexpr std::size_t pair_degree_threshold    = 5;
        static constexpr std::size_t sample_bitsize_limit     = 32;

        static constexpr bool crit_level_enabled              = false;
        static constexpr bool crit_apx_cells_enabled          = true;
        static constexpr bool crit_single_degree_enabled      = true;
        static constexpr bool crit_pair_degree_enabled        = true;
        static constexpr bool crit_apx_per_constraint_enabled = false;
        static constexpr bool crit_side_enabled               = false;
        static constexpr bool crit_sample_enabled             = false;
    };
    using Criteria = apx::Criteria<CriteriaSettings>;
};

struct OCSettings : smtrat::strategies::approximation::BaseOCSettings {
    using Criteria = ApxSettings::Criteria;
	using cell_apx_heuristic = cadcells::representation::cell_heuristics::InAndOutApproximation<ApxSettings>;
    using cell_heuristic = cadcells::representation::cell_heuristics::LowestDegreeBarriersFilter;
};

} // namespace internal

class Approximation_Outside : public Manager {
public:
	Approximation_Outside() : Manager() {
        setStrategy(
            addBackend<FPPModule<FPPSettings1>>({
                addBackend<STropModule<STropSettings3>>({
                    addBackend<SATModule<strategies::approximation::SATSettings<internal::OCSettings>>>()
                })
            })
        );
	}
};

} // namespace smtrat
