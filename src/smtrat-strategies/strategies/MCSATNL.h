#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSATNL: public Manager
	{
		public:
			MCSATNL(): Manager() {
				setStrategy(
					addBackend<SATModule<SATSettingsMCSATNL>>()
				);
			}
	};
}	// namespace smtrat
