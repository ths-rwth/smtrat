#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSAT_FMICPVSOCLWH13: public Manager
	{
		public:
			MCSAT_FMICPVSOCLWH13(): Manager() {
				setStrategy(
					addBackend<FPPModule<FPPSettings1>>(
						addBackend<SATModule<SATSettingsMCSATFMICPVSOCLWH13>>()
					)
				);
			}
	};
}	// namespace smtrat
