#pragma once

#include "../solver/Manager.h"

#include "../modules/LRAModule/LRAModule.h"
#include "../modules/PBPPModule/PBPPModule.h"
#include "../modules/SATModule/SATModule.h"


namespace smtrat
{
    class PBPPStrategyWithCardConstr:
        public Manager
    {
        public:
            PBPPStrategyWithCardConstr(): Manager() {
				setStrategy({
					addBackend<PBPPModule<PBPPSettingsWithCardConstr>>(
						addBackend<SATModule<SATSettings1>>(
							addBackend<LRAModule<LRASettings1>>()
						)
					),
				});
			}
    };
}    // namespace smtrat
