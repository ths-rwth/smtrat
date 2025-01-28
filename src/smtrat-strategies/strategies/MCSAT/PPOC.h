#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat {

class MCSAT_PPOC: public Manager {
public:
	MCSAT_PPOC(): Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>(
				addBackend<SATModule<SATSettingsMCSATOC>>()
			)
		);
	}
};

}	// namespace smtrat
