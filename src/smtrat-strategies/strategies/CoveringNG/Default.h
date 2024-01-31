#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {

/**
 * The most efficient CoveringNG strategy with preprocessing.
 * 
 */
class CoveringNG_Default: public Manager {
public:
	CoveringNG_Default() : Manager() {
		setStrategy(
            addBackend<CoveringNGModule<CoveringNGSettingsDefault>>()
        );
	}
};
} // namespace smtrat
