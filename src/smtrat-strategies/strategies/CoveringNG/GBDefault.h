#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/NewGBPPModule/NewGBPPModule.h>

#include <smtrat-solver/Manager.h>

namespace smtrat {
class CoveringNG_GBDefault: public Manager {
public:
	CoveringNG_GBDefault() : Manager() {
		setStrategy(
			addBackend<NewGBPPModule<NewGBPPSettings1>>({
				addBackend<CoveringNGModule<CoveringNGSettingsBase>>()
			})
        );
	}
};
} // namespace smtrat
