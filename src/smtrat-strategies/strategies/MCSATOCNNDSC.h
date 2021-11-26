#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATOCNNDSC: public Manager
	{
		public:
			MCSATOCNNDSC(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCNNDSC>>()
				);
			}
	};
}	// namespace smtrat
