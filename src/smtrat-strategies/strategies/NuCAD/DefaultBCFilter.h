#pragma once

#include <smtrat-modules/NuCADModule/NuCADModule.h>
#include <smtrat-modules/NuCADModule/NuCADModule.tpp>
#include <smtrat-solver/Manager.h>

namespace smtrat {

namespace internal {

struct mcf_settings : cadcells::operators::MccallumFilteredSettings {
    static constexpr DelineationFunction delineation_function = NOOP;
    static constexpr bool complete = true;
};

struct NuCADSettings : NuCADSettingsDefault  {
    using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellFilter;
    using op = cadcells::operators::MccallumFiltered<mcf_settings>;
};

}

class NuCAD_DefaultBCFilter: public Manager {
public:
	NuCAD_DefaultBCFilter() : Manager() {
		setStrategy(
            addBackend<NuCADModule<internal::NuCADSettings>>()
        );
	}
};
} // namespace smtrat
