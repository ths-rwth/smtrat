#pragma once

#include "../solver/Manager.h"

#include "../modules/LRAModule/LRAModule.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/PBPPModule/PBPPModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/ICPModule/ICPModule.h"
#include "../modules/VSModule/VSModule.h"
#include "../modules/CubeLIAModule/CubeLIAModule.h"



namespace smtrat
{
    class PBPPStrategyGroebner:
        public Manager
    {
        public:
            PBPPStrategyGroebner(): Manager() {
				setStrategy({
					//addBackend<FPPModule<FPPSettingsPB>>(
						//addBackend<PBPPModule<PBPPSettings1>>(
							addBackend<PBPPModule<PBPPSettings1>>(
							addBackend<FPPModule<FPPSettingsPB>>(
							addBackend<SATModule<SATSettings1>>(
								//addBackend<VSModule<VSSettings234>>(
								//addBackend<ICPModule<ICPSettings4>>(
									//addBackend<CubeLIAModule<CubeLIASettings1>>(
										addBackend<LRAModule<LRASettings1>>()
									//)
								//)
							)
						)
					)
				});
			}
    };
}    // namespace smtrat
