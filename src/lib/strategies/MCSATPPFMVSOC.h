#pragma once

#include "../solver/Manager.h"

#include "../modules/FPPModule/FPPModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class MCSATFMVSOC: public Manager
	{
		public:
			MCSATFMVSOC(): Manager() {
				setStrategy(
					addBackend<FPPModule<FPPSettings1>>(
						addBackend<SATModule<SATSettingsMCSATFMVSOC>>()
					)
				);
			}
	};
}	// namespace smtrat
