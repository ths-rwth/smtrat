#pragma once

#include "../solver/Manager.h"

#include "../modules/CADModule/CADModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class CADOnlyEarly: public Manager
	{
		public:
			CADOnlyEarly(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
						addBackend<CADModule<CADSettingsSplitEarly>>()
					})
				});
			}
	};

}	// namespace smtrat
