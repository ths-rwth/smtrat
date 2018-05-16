#pragma once

#include "../solver/Manager.h"

#include "../modules/NewCADModule/NewCADModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class NewCAD_LOLTSA: public Manager
	{
		public:
			NewCAD_LOLTSA(): Manager() {
				setStrategy(
					addBackend<SATModule<SATSettings1>>(
						addBackend<NewCADModule<NewCADSettings_LOLTSA>>()
					)
				);
			}
	};
}
