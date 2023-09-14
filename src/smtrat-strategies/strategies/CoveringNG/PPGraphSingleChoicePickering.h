#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
class CoveringNG_PPGraphSingleChoicePickering: public Manager {
public:
	CoveringNG_PPGraphSingleChoicePickering() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
                addBackend<CoveringNGModule<CoveringNGSettingsGraphSingleChoicePickering>>()
            })
        );
	}
};
} // namespace smtrat
