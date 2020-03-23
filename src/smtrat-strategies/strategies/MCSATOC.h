#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

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
