#pragma once

#include "../solver/Manager.h"

#include "../modules/CNFerModule/CNFerModule.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/NewCADModule/NewCADModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class NewCAD_FOS: public Manager
	{
		public:
			NewCAD_FOS(): Manager() {
				setStrategy(
					//addBackend<CNFerModule>(
					//	addBackend<FPPModule<FPPSettings1>>(
							addBackend<SATModule<SATSettings1>>(
								addBackend<NewCADModule<NewCADSettingsFOS>>()
							)
					//	)
					//)
				);
			}
	};
}	// namespace smtrat
