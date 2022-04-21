#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATFMICPOC: public Manager
	{
		public:
			MCSATFMICPOC(): Manager() {
				setStrategy(
					addBackend<FPPModule<FPPSettings1>>(
						addBackend<SATModule<SATSettingsMCSATFMICPOC>>()
					)
				);
			}
	};
}	// namespace smtrat
