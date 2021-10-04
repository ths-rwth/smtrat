#pragma once

#include <smtrat-solver/Manager.h>

#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATFMICPVSOCNewPP: public Manager
	{
		public:
			MCSATFMICPVSOCNewPP(): Manager() {
				setStrategy(
					addBackend<FPPModule<FPPSettings1>>(
						addBackend<SATModule<SATSettingsMCSATFMICPVSOCNew>>()
					)
				);
			}
	};
}	// namespace smtrat
