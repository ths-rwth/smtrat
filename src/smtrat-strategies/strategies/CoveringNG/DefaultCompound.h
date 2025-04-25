#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/CoveringNGModule/CoveringNGModule.tpp>
#include <smtrat-solver/Manager.h>

namespace smtrat {

namespace internal {

struct CoveringNGSettings : CoveringNGSettingsBase  {
    using cell_heuristic = cadcells::representation::cell_heuristics::AllCompound;
    using covering_heuristic = cadcells::representation::covering_heuristics::AllCompoundCovering;
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
