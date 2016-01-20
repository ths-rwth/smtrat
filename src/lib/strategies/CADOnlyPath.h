#pragma once

#include "../solver/Manager.h"

#include "../modules/CADModule/CADModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class CADOnlyPath: public Manager
	{
		public:
			CADOnlyPath(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
						addBackend<CADModule<CADSettingsSplitPath>>()
					})
				});
			}
	};
}	// namespace smtrat
