#pragma once

#include "../solver/Manager.h"

#include "../modules/LRAModule/LRAModule.h"
#include "../modules/PBPPModule/PBPPModule.h"
#include "../modules/SATModule/SATModule.h"


namespace smtrat
{
    class PBPPStrategyWithMixedConstr:
        public Manager
    {
        public:
            PBPPStrategyWithMixedConstr(): Manager() {
				setStrategy({
					addBackend<PBPPModule<PBPPSettingsWithMixedConstr>>(
						addBackend<SATModule<SATSettings1>>(
							addBackend<LRAModule<LRASettings1>>()
						)
					),
				});
			}
    };
}    // namespace smtrat
