#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSAT_OCLWH23: public Manager
	{
		public:
			MCSAT_OCLWH23(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCLWH23>>()
				);
			}
	};
}	// namespace smtrat
