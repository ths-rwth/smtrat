#pragma once

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSAT_FMVSNL: public Manager
	{
		public:
			MCSAT_FMVSNL(): Manager() {
				setStrategy(
					addBackend<FPPModule<FPPSettings1>>(
						addBackend<SATModule<SATSettingsMCSATFMVSNL>>()
					)
				);
			}
	};
}	// namespace smtrat
