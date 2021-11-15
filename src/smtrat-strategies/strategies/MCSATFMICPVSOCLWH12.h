#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATFMICPVSOCLWH12: public Manager
	{
		public:
			MCSATFMICPVSOCLWH12(): Manager() {
				setStrategy(
					addBackend<FPPModule<FPPSettings1>>(
						addBackend<SATModule<SATSettingsMCSATFMICPVSOCLWH12>>()
					)
				);
			}
	};
}	// namespace smtrat
