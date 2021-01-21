#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATOCNew: public Manager
	{
		public:
			MCSATOCNew(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCNew>>()
				);
			}
	};
}	// namespace smtrat
