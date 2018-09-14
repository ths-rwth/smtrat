#pragma once

#include "../solver/Manager.h"

//#include "../modules/FPPModule/FPPModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class MCSATOCNPP: public Manager
	{
		public:
			MCSATOCNPP(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOC>>()
				);
			}
	};
}	// namespace smtrat
