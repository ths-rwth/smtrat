#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSAT_FMVSOC: public Manager
	{
		public:
			MCSAT_FMVSOC(): Manager() {
				setStrategy(
					addBackend<FPPModule<FPPSettings1>>(
						addBackend<SATModule<SATSettingsMCSATFMVSOC>>()
					)
				);
			}
	};
}	// namespace smtrat
