#pragma once

#include "../solver/Manager.h"

#include "../modules/LRAModule/LRAModule.h"
#include "../modules/PBPPModule/PBPPModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/CubeLIAModule/CubeLIAModule.h"


namespace smtrat
{
    class PBPPStrategyLIAOnly:
        public Manager
    {
        public:
            PBPPStrategyLIAOnly(): Manager() {
				setStrategy({
					//addBackend<FPPModule<FPPSettingsPB>>(
					//addBackend<PBPPModule<PBPPSettingsLIAOnly>>(
					//addBackend<FPPModule<FPPSettingsPB>>(
                    
                        addBackend<SATModule<SATSettings1>>(
                        
                            addBackend<CubeLIAModule<CubeLIASettings1>>(
                            
                                addBackend<LRAModule<LRASettings1>>()
                            )
                        )
					//)
					//)
					//)
				});
			}
    };
}    // namespace smtrat
