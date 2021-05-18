#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATOCLWH32: public Manager
	{
		public:
			MCSATOCLWH32(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCLWH32>>()
				);
			}
	};
}	// namespace smtrat
