#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSAT_FMICPVSNL: public Manager
	{
		public:
			MCSAT_FMICPVSNL(): Manager() {
				setStrategy(
					addBackend<SATModule<SATSettingsMCSATFMICPVSNL>>()
				);
			}
	};
}	// namespace smtrat
