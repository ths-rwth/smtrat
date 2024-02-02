#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {

/**
 * The most efficient CoveringNG strategy with preprocessing.
 * 
 */
class CoveringNG_PPSATDefault: public Manager {
public:
	CoveringNG_PPSATDefault() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
				addBackend<SATModule<SATModule1>>({
                	addBackend<CoveringNGModule<CoveringNGSettingsDefault>>()
				})
            })
        );
	}
};
} // namespace smtrat
