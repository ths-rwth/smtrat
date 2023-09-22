#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/NewGBPPModule/NewGBPPModule.h>
#include <smtrat-modules/FPPModule/FPPModule.h>

#include <smtrat-solver/Manager.h>

namespace smtrat {
class CoveringNG_PPGBGraphSingleChoice: public Manager {
public:
	CoveringNG_PPGBGraphSingleChoice() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
				addBackend<NewGBPPModule<NewGBPPSettings1>>({
                	addBackend<CoveringNGModule<CoveringNGSettingsGraphSingleChoice>>()
				})
            })
        );
	}
};
} // namespace smtrat
