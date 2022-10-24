#pragma once

#include "../solver/Manager.h"

#include "../modules/CNFerModule/CNFerModule.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/NewCADModule/NewCADModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class NewCADEQ_BR: public Manager
	{
		public:
			NewCADEQ_BR(): Manager() {
				setStrategy(
					addBackend<SATModule<SATSettings1>>(
						addBackend<NewCADModule<NewCADSettingsEQ_BR>>()
					)
				);
			}
	};
}	// namespace smtrat
