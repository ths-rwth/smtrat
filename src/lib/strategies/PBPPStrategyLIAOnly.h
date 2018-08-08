#pragma once

#include "../solver/Manager.h"

#include "../modules/LRAModule/LRAModule.h"
#include "../modules/PBPPModule/PBPPModule.h"
#include "../modules/SATModule/SATModule.h"


namespace smtrat
{
    class PBPPStrategyLIAOnly:
        public Manager
    {
        public:
            PBPPStrategyLIAOnly(): Manager() {
				setStrategy({
					addBackend<PBPPModule<PBPPSettingsLIAOnly>>(
						addBackend<SATModule<SATSettings1>>(
							addBackend<LRAModule<LRASettings1>>()
						)
					),
				});
			}
    };
}    // namespace smtrat
