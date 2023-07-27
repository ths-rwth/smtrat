#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
class CoveringNG_GraphSingle: public Manager {
public:
	CoveringNG_GraphSingle() : Manager() {
		setStrategy(
            addBackend<CoveringNGModule<CoveringNGSettingsGraphSingle>>()
        );
	}
};
} // namespace smtrat
