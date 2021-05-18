#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATOCLWH12: public Manager
	{
		public:
			MCSATOCLWH12(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCLWH12>>()
				);
			}
	};
}	// namespace smtrat
