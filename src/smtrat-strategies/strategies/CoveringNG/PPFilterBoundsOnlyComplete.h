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

struct CoveringNGSettings : CoveringNGSettingsDefault  {
    using op = cadcells::operators::MccallumFiltered<OpSettings>;
    constexpr static auto cell_heuristic = cadcells::representation::BIGGEST_CELL_FILTER;
    constexpr static auto covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_FILTER;
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
