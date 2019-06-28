#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/CADIntervalModule/CADIntervalModule.h>
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class CADIntervalBased: public Manager
	{
		public:
			CADIntervalBased(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
						addBackend<CADIntervalModule<CADIntervalSettingsBase>>()
					})
				});
			}
	};
}	// namespace smtrat
