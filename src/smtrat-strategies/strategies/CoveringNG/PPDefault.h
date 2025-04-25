#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {

/**
 * The most efficient CoveringNG strategy with preprocessing.
 * 
 */
class CoveringNG_PPDefault: public Manager {
public:
	CoveringNG_PPDefault() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
                addBackend<CoveringNGModule<CoveringNGSettingsBase>>()
            })
        );
	}
};
} // namespace smtrat
