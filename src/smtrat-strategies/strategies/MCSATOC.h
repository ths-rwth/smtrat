#pragma once

#include "../solver/Manager.h"

//#include "../modules/FPPModule/FPPModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class MCSATOC: public Manager
	{
		public:
			MCSATOC(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOC>>()
				);
			}
	};
}	// namespace smtrat
