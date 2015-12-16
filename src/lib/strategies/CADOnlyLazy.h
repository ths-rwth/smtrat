#pragma once

#include "../solver/Manager.h"

#include "../modules/CADModule/CADModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class CADOnlyLazy: public Manager
	{
		public:
			CADOnlyLazy(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
						addBackend<CADModule<CADSettingsSplitLazy>>()
					})
				});
			}
	};
}	// namespace smtrat
