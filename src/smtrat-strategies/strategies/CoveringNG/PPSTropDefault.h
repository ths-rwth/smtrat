#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/STropModule/STropModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {

/**
 * The most efficient CoveringNG strategy with preprocessing and subtropical. Is slightly slower than PPDefault.
 * 
 */
class CoveringNG_PPSTropDefault: public Manager {
public:
	CoveringNG_PPSTropDefault() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
                addBackend<STropModule<STropSettings3>>({
                    addBackend<CoveringNGModule<CoveringNGSettingsBase>>()
                })
            })
        );
	}
};
} // namespace smtrat
