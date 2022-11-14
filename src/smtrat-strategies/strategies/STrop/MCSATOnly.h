#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class STrop_MCSATOnly: public Manager
	{
		public:
			STrop_MCSATOnly(): Manager() {
				setStrategy({
					addBackend<FPPModule<FPPSettings1>>({
						addBackend<SATModule<SATSettingsMCSATFMICPVSOCNewOC>>()
					})
				});
			}
	};
}	// namespace smtrat
