#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
class CoveringNG_PPGraphSingleChoiceFact: public Manager {
public:
	CoveringNG_PPGraphSingleChoiceFact() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
                addBackend<CoveringNGModule<CoveringNGSettingsGraphSingleChoiceFact>>()
            })
        );
	}
};
} // namespace smtrat
