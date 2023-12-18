#pragma once

#include "OCNew.h"

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {

class MCSAT_PPOCNew : public Manager {
public:
	MCSAT_PPOCNew()
		: Manager() {
		setStrategy(
			addBackend<SATModule<SATSettingsMCSATDefault>>());
	}
};

} // namespace smtrat
