#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSAT_OCLWH21: public Manager
	{
		public:
			MCSAT_OCLWH21(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCLWH21>>()
				);
			}
	};
}	// namespace smtrat
