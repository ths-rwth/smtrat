#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
class CoveringNG_PPGraphSingleChoiceLDB: public Manager {
public:
	CoveringNG_PPGraphSingleChoiceLDB() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
                addBackend<CoveringNGModule<CoveringNGSettingsGraphSingleChoiceLDB>>()
            })
        );
	}
};
} // namespace smtrat
