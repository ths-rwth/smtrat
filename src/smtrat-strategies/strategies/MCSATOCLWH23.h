#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATOCLWH23: public Manager
	{
		public:
			MCSATOCLWH23(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCLWH23>>()
				);
			}
	};
}	// namespace smtrat
