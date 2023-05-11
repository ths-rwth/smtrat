#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
class CoveringNG_PPExImplicantsMulti: public Manager {
public:
	CoveringNG_PPExImplicantsMulti() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
                addBackend<CoveringNGModule<CoveringNGSettingsExImplicantsMulti>>()
            })
        );
	}
};
} // namespace smtrat
