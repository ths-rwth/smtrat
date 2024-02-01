#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/CoveringNGModule/CoveringNGModule.tpp>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {


namespace internal {

struct CoveringNGSettings : CoveringNGSettingsDefault  {
    using op = cadcells::operators::MccallumFiltered<cadcells::operators::MccallumFilteredSettings>;
    constexpr static auto cell_heuristic = cadcells::representation::BIGGEST_CELL_FILTER;
    constexpr static auto covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_FILTER;
};

}

class CoveringNG_PPFilterNoop: public Manager {
public:
	CoveringNG_PPFilterNoop() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
                addBackend<CoveringNGModule<internal::CoveringNGSettings>>()
            })
        );
	}
};
} // namespace smtrat
