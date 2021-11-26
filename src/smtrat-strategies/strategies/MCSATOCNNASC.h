#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATOCNNASC: public Manager
	{
		public:
			MCSATOCNNASC(): Manager() {
				setStrategy(
						addBackend<SATModule<SATSettingsMCSATOCNNASC>>()
				);
			}
	};
}	// namespace smtrat
