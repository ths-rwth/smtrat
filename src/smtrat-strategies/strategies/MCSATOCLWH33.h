#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATOCLWH33: public Manager
	{
		public:
			MCSATOCLWH33(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCLWH33>>()
				);
			}
	};
}	// namespace smtrat
