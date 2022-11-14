#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSAT_OCPARALLEL: public Manager
	{
		public:
			MCSAT_OCPARALLEL(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCPARALLEL>>()
				);
			}
	};
}	// namespace smtrat
