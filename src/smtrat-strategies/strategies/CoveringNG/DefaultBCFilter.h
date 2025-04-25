#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/CoveringNGModule/CoveringNGModule.tpp>
#include <smtrat-solver/Manager.h>

namespace smtrat {

namespace internal {

struct mcf_settings : cadcells::operators::MccallumFilteredCompleteSettings {
    static constexpr DelineationFunction delineation_function = NOOP;
};

struct CoveringNGSettings : CoveringNGSettingsBase  {
    using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellFilter;
    using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringFilter;
    using op = cadcells::operators::MccallumFiltered<mcf_settings>;
};

}

class CoveringNG_DefaultBCFilter: public Manager {
public:
	CoveringNG_DefaultBCFilter() : Manager() {
		setStrategy(
            addBackend<CoveringNGModule<internal::CoveringNGSettings>>()
        );
	}
};
} // namespace smtrat
