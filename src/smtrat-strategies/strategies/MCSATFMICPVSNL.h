#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATFMICPVSNL: public Manager
	{
		public:
			MCSATFMICPVSNL(): Manager() {
				setStrategy(
					addBackend<SATModule<SATSettingsMCSATFMICPVSNL>>()
				);
			}
	};
}	// namespace smtrat
