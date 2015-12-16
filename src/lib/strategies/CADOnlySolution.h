#pragma once

#include "../solver/Manager.h"

#include "../modules/CADModule/CADModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class CADOnlySolution: public Manager
	{
		public:
			CADOnlySolution(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
						addBackend<CADModule<CADSettingsSplitSolution>>()
					})
				});
			}
	};
}	// namespace smtrat
