#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATICPNL: public Manager
	{
		public:
			MCSATICPNL(): Manager() {
				setStrategy(
					addBackend<SATModule<SATSettingsMCSATICPNL>>()
				);
			}
	};
}	// namespace smtrat
