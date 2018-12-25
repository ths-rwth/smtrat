#pragma once

#include "../solver/Manager.h"

#include "../modules/CNFerModule/CNFerModule.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/NewCADModule/NewCADModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class NewCADEQ_SID: public Manager
	{
		public:
			NewCADEQ_SID(): Manager() {
				setStrategy(
					addBackend<SATModule<SATSettings1>>(
						addBackend<NewCADModule<NewCADSettingsEQ_SID>>()
					)
				);
			}
	};
}	// namespace smtrat
