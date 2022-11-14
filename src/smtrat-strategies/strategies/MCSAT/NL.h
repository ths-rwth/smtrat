#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSAT_NL: public Manager
	{
		public:
			MCSAT_NL(): Manager() {
				setStrategy(
					addBackend<SATModule<SATSettingsMCSATNL>>()
				);
			}
	};
}	// namespace smtrat
