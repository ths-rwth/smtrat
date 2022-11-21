#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
class CoveringNG_PPMinLvlMinTdeg: public Manager {
public:
	CoveringNG_PPMinLvlMinTdeg() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
                addBackend<CoveringNGModule<CoveringNGSettingsMinLvlMinTdeg>>()
            })
        );
	}
};
} // namespace smtrat
