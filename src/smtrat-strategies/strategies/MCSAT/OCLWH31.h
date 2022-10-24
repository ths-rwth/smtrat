#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSAT_OCLWH31: public Manager
	{
		public:
			MCSAT_OCLWH31(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCLWH31>>()
				);
			}
	};
}	// namespace smtrat
