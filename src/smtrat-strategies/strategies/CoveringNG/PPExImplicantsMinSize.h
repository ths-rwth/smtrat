#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
class CoveringNG_PPExImplicantsMinSize: public Manager {
public:
	CoveringNG_PPExImplicantsMinSize() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
                addBackend<CoveringNGModule<CoveringNGSettingsExImplicantsMinSize>>()
            })
        );
	}
};
} // namespace smtrat
