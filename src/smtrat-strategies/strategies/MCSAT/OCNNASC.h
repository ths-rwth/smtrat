#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSAT_OCNNASC: public Manager
	{
		public:
			MCSAT_OCNNASC(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCNNASC>>()
				);
			}
	};
}	// namespace smtrat
