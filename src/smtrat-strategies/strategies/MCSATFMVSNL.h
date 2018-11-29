#pragma once

#include "../solver/Manager.h"

#include "../modules/FPPModule/FPPModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class MCSATFMVSNL: public Manager
	{
		public:
			MCSATFMVSNL(): Manager() {
				setStrategy(
					addBackend<FPPModule<FPPSettings1>>(
						addBackend<SATModule<SATSettingsMCSATFMVSNL>>()
					)
				);
			}
	};
}	// namespace smtrat
