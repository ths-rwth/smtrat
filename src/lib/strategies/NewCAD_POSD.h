#pragma once

#include "../solver/Manager.h"

#include "../modules/NewCADModule/NewCADModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class NewCAD_POSD: public Manager
	{
		public:
			NewCAD_POSD(): Manager() {
				setStrategy(
					addBackend<SATModule<SATSettings1>>(
						addBackend<NewCADModule<NewCADSettings_POSD>>()
					)
				);
			}
	};
}
