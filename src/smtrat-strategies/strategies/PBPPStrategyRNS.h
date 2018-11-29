#pragma once

#include "../solver/Manager.h"

#include "../modules/LRAModule/LRAModule.h"
#include "../modules/PBPPModule/PBPPModule.h"
#include "../modules/SATModule/SATModule.h"


namespace smtrat
{
    class PBPPStrategyRNS:
        public Manager
    {
        public:
            PBPPStrategyRNS(): Manager() {
				setStrategy({
					addBackend<PBPPModule<PBPPSettingsWithRNS>>(
						addBackend<SATModule<SATSettings1>>(
							addBackend<LRAModule<LRASettings1>>()
						)
					),
				});
			}
    };
}    // namespace smtrat
