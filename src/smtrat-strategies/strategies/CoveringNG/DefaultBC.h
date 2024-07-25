#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/CoveringNGModule/CoveringNGModule.tpp>
#include <smtrat-solver/Manager.h>

namespace smtrat {

namespace internal {

struct CoveringNGSettings : CoveringNGSettingsDefault  {
    using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCell;
    using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCovering;
};

}

class CoveringNG_DefaultBC: public Manager {
public:
	CoveringNG_DefaultBC() : Manager() {
		setStrategy(
            addBackend<CoveringNGModule<internal::CoveringNGSettings>>()
        );
	}
};
} // namespace smtrat
