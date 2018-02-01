#pragma once

#include "../solver/Manager.h"

#include "../modules/NewCADModule/NewCADModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class NewCADFU_SCS: public Manager
	{
		public:
			NewCADFU_SCS(): Manager() {
				setStrategy(
					addBackend<SATModule<SATSettings1>>(
						addBackend<NewCADModule<NewCADSettingsFU_SCS>>()
					)
				);
			}
	};
}
