#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/CoveringNGModule/CoveringNGModule.tpp>
#include <smtrat-solver/Manager.h>

namespace smtrat {

namespace internal {

struct mcf_settings : cadcells::operators::MccallumFilteredSettings {
    static constexpr DelineationFunction delineation_function = NOOP;
};

struct CoveringNGSettings : CoveringNGSettingsDefault  {
    static constexpr cadcells::representation::CellHeuristic cell_heuristic = cadcells::representation::BIGGEST_CELL_FILTER;
    static constexpr cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::BIGGEST_CELL_APX;
    using op = cadcells::operators::MccallumFiltered<mcf_settings>;
};

}

class CoveringNG_DefaultAPX: public Manager {
public:
	CoveringNG_DefaultAPX() : Manager() {
		setStrategy(
            addBackend<CoveringNGModule<internal::CoveringNGSettings>>()
        );
	}
};
} // namespace smtrat
