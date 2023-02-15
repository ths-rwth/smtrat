#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
class CoveringNG_PPExImplicantsPruning: public Manager {
public:
	CoveringNG_PPExImplicantsPruning() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
                addBackend<CoveringNGModule<CoveringNGSettingsExImplicantsPruning>>()
            })
        );
	}
};
} // namespace smtrat
