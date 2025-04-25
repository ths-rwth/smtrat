#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/CoveringNGModule/CoveringNGModule.tpp>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {


namespace internal {

struct OpSettings : cadcells::operators::MccallumFilteredSettings {
	static constexpr DelineationFunction delineation_function = BOUNDS_ONLY;
    static constexpr bool enable_weak = true;
    static constexpr bool complete = true;
};

struct CoveringNGSettings : CoveringNGSettingsBase  {
    using op = cadcells::operators::MccallumFiltered<OpSettings>;
    using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellFilter;
    using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringFilter;
};

}

class CoveringNG_PPFilterBoundsOnlyComplete: public Manager {
public:
	CoveringNG_PPFilterBoundsOnlyComplete() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
                addBackend<CoveringNGModule<internal::CoveringNGSettings>>()
            })
        );
	}
};
} // namespace smtrat
