#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
class CoveringNG_PPGraphSingleChoicePostprocess: public Manager {
public:
	CoveringNG_PPGraphSingleChoicePostprocess() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
                addBackend<CoveringNGModule<CoveringNGSettingsGraphSingleChoicePostprocess>>()
            })
        );
	}
};
} // namespace smtrat
