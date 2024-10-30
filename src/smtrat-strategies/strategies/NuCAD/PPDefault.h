#pragma once

#include <smtrat-modules/NuCADModule/NuCADModule.h>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {

class NuCAD_PPDefault: public Manager {
public:
	NuCAD_PPDefault() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
                addBackend<NuCADModule<NuCADSettingsDefault>>()
            })
        );
	}
};
} // namespace smtrat
