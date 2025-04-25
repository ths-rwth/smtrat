#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/CoveringNGModule/CoveringNGModule.tpp>
#include <smtrat-solver/Manager.h>

namespace smtrat {

namespace internal {

struct mcf_settings : cadcells::operators::MccallumFilteredSettings {
    static constexpr DelineationFunction delineation_function = NOOP;
    static constexpr bool complete = false;
};

struct CoveringNGSettings : CoveringNGSettingsBase  {
    using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellFilter;
    using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringFilter;
    using op = cadcells::operators::MccallumFiltered<mcf_settings>;
};

}

class CoveringNG_DefaultBCFilterIncomplete: public Manager {
public:
    CoveringNG_DefaultBCFilterIncomplete() : Manager() {
		setStrategy(
            addBackend<CoveringNGModule<internal::CoveringNGSettings>>()
        );
	}
};
} // namespace smtrat
