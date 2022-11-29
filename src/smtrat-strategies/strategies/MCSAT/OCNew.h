#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSAT_OCNew: public Manager
	{
		public:
			MCSAT_OCNew(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCNew>>()
				);
			}
	};
}	// namespace smtrat
