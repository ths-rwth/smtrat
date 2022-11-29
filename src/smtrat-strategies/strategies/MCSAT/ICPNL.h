#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSAT_ICPNL: public Manager
	{
		public:
			MCSAT_ICPNL(): Manager() {
				setStrategy(
					addBackend<SATModule<SATSettingsMCSATICPNL>>()
				);
			}
	};
}	// namespace smtrat
