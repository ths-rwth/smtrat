#pragma once

#include "../solver/Manager.h"

#include "../modules/CNFerModule/CNFerModule.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/NewCADModule/NewCADModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class NewCADEQ_BRI: public Manager
	{
		public:
			NewCADEQ_BRI(): Manager() {
				setStrategy(
					addBackend<SATModule<SATSettings1>>(
						addBackend<NewCADModule<NewCADSettingsEQ_BRI>>()
					)
				);
			}
	};
}	// namespace smtrat
