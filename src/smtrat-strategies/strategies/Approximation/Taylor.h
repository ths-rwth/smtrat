#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/SATModule/SATModule.tpp>
#include <smtrat-modules/STropModule/STropModule.h>

#include "common.h"

namespace smtrat {

namespace internal {

struct TaylorSettings {
	static constexpr std::size_t taylor_deg = 1;
	using Sampling = apx::SampleSimple;
};

struct ApxSettings {
    using method = apx::Taylor<TaylorSettings>;
    struct CriteriaSettings : apx::BaseCriteriaSettings {
        static constexpr std::size_t approximated_cells_limit = 100;
        static constexpr std::size_t single_degree_threshold  = 3;
        static constexpr std::size_t dynamic_degree_scale     = 2;
    };
    using Criteria = apx::Criteria<CriteriaSettings>;
};

struct OCSettings : smtrat::strategies::approximation::BaseOCSettings {
    using Criteria = ApxSettings::Criteria;
	using cell_apx_heuristic = cadcells::representation::cell_heuristics::BiggestCellApproximation<ApxSettings>;
};

} // namespace internal

class Approximation_Taylor : public Manager {
public:
	Approximation_Taylor() : Manager() {
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
