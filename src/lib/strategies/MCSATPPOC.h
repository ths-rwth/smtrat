#pragma once

#include "../solver/Manager.h"

#include "../modules/FPPModule/FPPModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class MCSATPPOC: public Manager
	{
		public:
			MCSATPPOC(): Manager() {
				setStrategy(
					addBackend<FPPModule<FPPSettings1>>(
						addBackend<SATModule<SATSettingsMCSATOC>>()
					)
				);
			}
	};
}	// namespace smtrat
