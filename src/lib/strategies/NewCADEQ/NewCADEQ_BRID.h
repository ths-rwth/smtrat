#pragma once

#include "../solver/Manager.h"

#include "../modules/CNFerModule/CNFerModule.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/NewCADModule/NewCADModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class NewCADEQ_BRID: public Manager
	{
		public:
			NewCADEQ_BRID(): Manager() {
				setStrategy(
					addBackend<SATModule<SATSettings1>>(
						addBackend<NewCADModule<NewCADSettingsEQ_BRID>>()
					)
				);
			}
	};
}	// namespace smtrat
