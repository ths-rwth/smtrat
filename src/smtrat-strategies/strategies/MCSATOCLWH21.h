#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATOCLWH21: public Manager
	{
		public:
			MCSATOCLWH21(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCLWH21>>()
				);
			}
	};
}	// namespace smtrat
