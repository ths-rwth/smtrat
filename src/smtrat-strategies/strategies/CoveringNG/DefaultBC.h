#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/CoveringNGModule/CoveringNGModule.tpp>
#include <smtrat-solver/Manager.h>

namespace smtrat {

namespace internal {

struct CoveringNGSettings : CoveringNGSettingsDefault  {
    using cell_heuristic = cadcells::representation::cell_heuristics::biggest_cell;
    using covering_heuristic = cadcells::representation::covering_heuristics::biggest_cell_covering;
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
