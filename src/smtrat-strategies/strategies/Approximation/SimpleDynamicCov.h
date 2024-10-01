#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/SATModule/SATModule.tpp>
#include <smtrat-modules/STropModule/STropModule.h>

#include "common.h"

namespace smtrat {

namespace internal {

struct CellApxSettings {
    using method = apx::Simple<apx::SimpleSettings>;
    struct CriteriaSettings : apx::BaseCriteriaSettings {
        static constexpr std::size_t approximated_cells_limit = 100;
        static constexpr std::size_t single_degree_threshold  = 3;
        static constexpr std::size_t dynamic_degree_scale     = 2;
    };
    using Criteria = apx::Criteria<CriteriaSettings>;
};

struct CoveringApxSettings {
    using method = apx::Simple<apx::SimpleSettings>;
    struct CriteriaSettings : apx::BaseCriteriaSettings {
        static constexpr std::size_t approximated_cells_limit = 5;
        static constexpr std::size_t blocking                 = 1;
        static constexpr std::size_t blocking_increment       = 1;
        static constexpr std::size_t single_degree_threshold  = 4;
        static constexpr std::size_t dynamic_degree_scale     = 0;
        static constexpr std::size_t pair_degree_threshold    = 7;
        static constexpr std::size_t sample_bitsize_limit     = 32;

        static constexpr bool crit_pair_degree_enabled        = true;
        static constexpr bool crit_sample_enabled             = true;
    };
    using Criteria = apx::Criteria<CriteriaSettings>;
};


struct OCSettings : smtrat::strategies::approximation::BaseOCSettings {
    using Criteria = CellApxSettings::Criteria;
	using cell_apx_heuristic = cadcells::representation::cell_heuristics::BiggestCellApproximation<CellApxSettings>;
    using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellAPXCovering<CoveringApxSettings>;
};

} // namespace internal

class Approximation_SimpleDynamic : public Manager {
public:
	Approximation_SimpleDynamic() : Manager() {
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
