#pragma once

#include <smtrat-modules/NuCADModule/NuCADModule.h>
#include <smtrat-modules/NuCADModule/NuCADModule.tpp>
#include <smtrat-solver/Manager.h>

namespace smtrat {

namespace internal {

struct mcf_settings : cadcells::operators::MccallumFilteredSettings {
    static constexpr DelineationFunction delineation_function = BOUNDS_ONLY;
	static constexpr bool enable_weak = true;
    static constexpr bool complete = true;
};

struct NuCADSettings : NuCADSettingsDefault  {
    using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellFilter;
    using op = cadcells::operators::MccallumFiltered<mcf_settings>;
    static constexpr bool enable_weak = true;
};

}

class NuCAD_DefaultBCFilterEW: public Manager {
public:
	NuCAD_DefaultBCFilterEW() : Manager() {
		setStrategy(
            addBackend<NuCADModule<internal::NuCADSettings>>()
        );
	}
};
} // namespace smtrat
