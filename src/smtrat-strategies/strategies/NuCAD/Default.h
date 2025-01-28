#pragma once

#include <smtrat-modules/NuCADModule/NuCADModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {

class NuCAD_Default: public Manager {
public:
	NuCAD_Default() : Manager() {
		setStrategy(
            addBackend<NuCADModule<NuCADSettingsDefault>>()
        );
	}
};
} // namespace smtrat
