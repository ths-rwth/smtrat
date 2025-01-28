#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/CoveringNGModule/CoveringNGModule.tpp>
#include <smtrat-solver/Manager.h>

namespace smtrat {

namespace internal {

struct mcf_settings : cadcells::operators::MccallumFilteredSettings {
    static constexpr DelineationFunction delineation_function = NOOP;
};

namespace apx = cadcells::representation::approximation;

struct APXSettings {
	using Criteria = apx::ApxCriteria<typename apx::BaseCriteriaSettings>;
};

struct CoveringNGSettings : CoveringNGSettingsDefault  {
    using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellFilter;
    using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellAPXCovering<APXSettings>;
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
