#pragma once

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {

class MCSAT_PPDefault : public Manager {
public:
	MCSAT_PPDefault() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
				addBackend<SATModule<SATSettingsMCSATVSIDS>>()
			})
		);
	}
};

} // namespace smtrat
