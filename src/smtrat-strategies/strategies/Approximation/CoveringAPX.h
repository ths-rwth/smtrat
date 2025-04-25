#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/CoveringNGModule/CoveringNGModule.tpp>
#include <smtrat-solver/Manager.h>

namespace smtrat {

namespace internal {

struct mcf_settings : cadcells::operators::MccallumFilteredSettings {
    static constexpr DelineationFunction delineation_function = NOOP;
};

namespace apx = cadcells::representation::approximation;

struct APXSettings {
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

struct CoveringNGSettings : CoveringNGSettingsBase  {
    using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellFilter;
    using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellAPXCovering<APXSettings>;
    using op = cadcells::operators::MccallumFiltered<mcf_settings>;
};

}

class Approximation_CoveringAPX: public Manager {
public:
	Approximation_CoveringAPX() : Manager() {
		setStrategy(
            addBackend<CoveringNGModule<internal::CoveringNGSettings>>()
        );
	}
};
} // namespace smtrat
