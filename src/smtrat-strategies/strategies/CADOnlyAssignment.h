#pragma once

#include "../solver/Manager.h"

#include "../modules/CADModule/CADModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class CADOnlyAssignment: public Manager
	{
		public:
			CADOnlyAssignment(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
						addBackend<CADModule<CADSettingsSplitAssignment>>()
					})
				});
			}
	};

}	// namespace smtrat
