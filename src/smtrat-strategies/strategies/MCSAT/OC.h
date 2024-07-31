#pragma once

#include <smtrat-solver/Manager.h>
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat {

class MCSAT_OC: public Manager {
public:
	MCSAT_OC(): Manager() {
		setStrategy(
				addBackend<SATModule<SATSettingsMCSATOC>>()
		);
	}
};

}	// namespace smtrat
