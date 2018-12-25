#pragma once

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATFMVSNL: public Manager
	{
		public:
			MCSATFMVSNL(): Manager() {
				setStrategy(
					addBackend<FPPModule<FPPSettings1>>(
						addBackend<SATModule<SATSettingsMCSATFMVSNL>>()
					)
				);
			}
	};
}	// namespace smtrat
