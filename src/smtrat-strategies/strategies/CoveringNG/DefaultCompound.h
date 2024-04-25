#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/CoveringNGModule/CoveringNGModule.tpp>
#include <smtrat-solver/Manager.h>

namespace smtrat {

namespace internal {

struct CoveringNGSettings : CoveringNGSettingsDefault  {
    static constexpr cadcells::representation::CellHeuristic cell_heuristic = cadcells::representation::ALL_COMPOUND;
    static constexpr cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::ALL_COMPOUND_COVERING;
};

}

class CoveringNG_DefaultCompound: public Manager {
public:
	CoveringNG_DefaultCompound() : Manager() {
		setStrategy(
            addBackend<CoveringNGModule<internal::CoveringNGSettings>>()
        );
	}
};
} // namespace smtrat
