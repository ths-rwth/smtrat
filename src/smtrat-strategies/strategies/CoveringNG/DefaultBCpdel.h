#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/CoveringNGModule/CoveringNGModule.tpp>
#include <smtrat-solver/Manager.h>

namespace smtrat {

namespace internal {

struct CoveringNGSettings : CoveringNGSettingsDefault  {
    using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellPdel;
    using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringPdel;
    using op = cadcells::operators::MccallumPdel<cadcells::operators::MccallumPdelSettingsComplete>;
};

}

class CoveringNG_DefaultBCpdel: public Manager {
public:
	CoveringNG_DefaultBCpdel() : Manager() {
		setStrategy(
            addBackend<CoveringNGModule<internal::CoveringNGSettings>>()
        );
	}
};
} // namespace smtrat
