#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSAT_OCNNDSC: public Manager
	{
		public:
			MCSAT_OCNNDSC(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCNNDSC>>()
				);
			}
	};
}	// namespace smtrat
