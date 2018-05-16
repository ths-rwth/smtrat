#pragma once

#include "../solver/Manager.h"

#include "../modules/FPPModule/FPPModule.h"
#include "../modules/IncWidthModule/IncWidthModule.h"
#include "../modules/IntBlastModule/IntBlastModule.h"
#include "../modules/ICPModule/ICPModule.h"
#include "../modules/VSModule/VSModule.h"
#include "../modules/LRAModule/LRAModule.h"
#include "../modules/NewCADModule/NewCADModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class NewCADOnly: public Manager
	{
		public:
			NewCADOnly(): Manager() {
				setStrategy(
					addBackend<FPPModule<FPPSettings1>>(
						addBackend<SATModule<SATSettings1>>(
							//addBackend<ICPModule<ICPSettings1>>(
								addBackend<VSModule<VSSettings234>>(
									addBackend<NewCADModule<NewCADSettingsConfigured>>()
								)
							//)
						)
					)
				);
			}
	};
}
