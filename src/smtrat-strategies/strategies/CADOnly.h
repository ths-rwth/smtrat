#pragma once

#include "../solver/Manager.h"

#include "../modules/CADModule/CADModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class CADOnly: public Manager
	{
		public:
			CADOnly(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
						addBackend<CADModule<CADSettingsReal>>()
					})
				});
			}
	};
}	// namespace smtrat
