#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATOCLWH22: public Manager
	{
		public:
			MCSATOCLWH22(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCLWH22>>()
				);
			}
	};
}	// namespace smtrat
