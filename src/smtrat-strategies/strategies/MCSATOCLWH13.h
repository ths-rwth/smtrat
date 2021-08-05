#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATOCLWH13: public Manager
	{
		public:
			MCSATOCLWH13(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCLWH13>>()
				);
			}
	};
}	// namespace smtrat
