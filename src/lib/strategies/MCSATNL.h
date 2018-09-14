#pragma once

#include "../solver/Manager.h"

#include "../modules/FPPModule/FPPModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class MCSATNL: public Manager
	{
		public:
			MCSATNL(): Manager() {
				setStrategy(
					addBackend<FPPModule<FPPSettings1>>(
						addBackend<SATModule<SATSettingsMCSATNL>>()
					)
				);
			}
	};
}	// namespace smtrat
