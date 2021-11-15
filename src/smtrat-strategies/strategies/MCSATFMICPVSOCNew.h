#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATFMICPVSOCNew: public Manager
	{
		public:
			MCSATFMICPVSOCNew(): Manager() {
				setStrategy(
					addBackend<FPPModule<FPPSettings1>>(
						addBackend<SATModule<SATSettingsMCSATFMICPVSOCNew>>()
					)
				);
			}
	};
}	// namespace smtrat
