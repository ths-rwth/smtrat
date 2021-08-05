#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATOCLWH11: public Manager
	{
		public:
			MCSATOCLWH11(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCLWH11>>()
				);
			}
	};
}	// namespace smtrat
