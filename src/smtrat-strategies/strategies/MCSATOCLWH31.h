#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATOCLWH31: public Manager
	{
		public:
			MCSATOCLWH31(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCLWH31>>()
				);
			}
	};
}	// namespace smtrat
