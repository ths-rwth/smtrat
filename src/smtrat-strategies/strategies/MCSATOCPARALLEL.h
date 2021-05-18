#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATOCPARALLEL: public Manager
	{
		public:
			MCSATOCPARALLEL(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCPARALLEL>>()
				);
			}
	};
}	// namespace smtrat
