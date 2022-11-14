#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSAT_OCNN: public Manager
	{
		public:
			MCSAT_OCNN(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCNN>>()
				);
			}
	};
}	// namespace smtrat
