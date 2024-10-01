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
        static constexpr std::size_t apx_per_constraint_limit = 5;
        static constexpr double      involved_constraint_scale = 0.3;  
        static constexpr std::size_t single_degree_threshold  = 5;

        static constexpr bool crit_apx_cells_enabled          = false;
        static constexpr bool crit_apx_per_constraint_enabled = true;
    };
    using Criteria = apx::Criteria<CriteriaSettings>;
};

struct OCSettings : smtrat::strategies::approximation::BaseOCSettings {
    using Criteria = ApxSettings::Criteria;
	using cell_apx_heuristic = cadcells::representation::cell_heuristics::BiggestCellApproximation<ApxSettings>;
};

} // namespace internal

class Approximation_SimpleConstraints : public Manager {
public:
	Approximation_SimpleConstraints() : Manager() {
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
