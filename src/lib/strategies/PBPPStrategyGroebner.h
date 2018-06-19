#pragma once

#include "../solver/Manager.h"

#include "../modules/LRAModule/LRAModule.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/PBPPModule/PBPPModule.h"
#include "../modules/SATModule/SATModule.h"


namespace smtrat
{
    class PBPPStrategyGroebner:
        public Manager
    {
        public:
            PBPPStrategyGroebner(): Manager() {
				setStrategy({
					addBackend<FPPModule<FPPSettingsPB>>(
						addBackend<PBPPModule<PBPPSettings1>>(
							addBackend<SATModule<SATSettings1>>(
								addBackend<LRAModule<LRASettings1>>()
							)
						)
					)
				});
			}
    };
}    // namespace smtrat
