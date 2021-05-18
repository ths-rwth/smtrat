#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATOCNN: public Manager
	{
		public:
			MCSATOCNN(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCNN>>()
				);
			}
	};
}	// namespace smtrat
