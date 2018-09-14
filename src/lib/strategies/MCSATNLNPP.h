#pragma once

#include "../solver/Manager.h"

//#include "../modules/FPPModule/FPPModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	//no preprocessing
	class MCSATNLNPP: public Manager
	{
		public:
			MCSATNLNPP(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATNL>>()
				);
			}
	};
}	// namespace smtrat
