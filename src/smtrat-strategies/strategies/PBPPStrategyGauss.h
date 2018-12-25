#pragma once

#include "../solver/Manager.h"

#include "../modules/LRAModule/LRAModule.h"
#include "../modules/PBPPModule/PBPPModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/PBGaussModule/PBGaussModule.h"


namespace smtrat
{
    class PBPPStrategyGauss:
    public Manager
    {
    public:
        PBPPStrategyGauss(): Manager() {
            setStrategy({
                addBackend<PBGaussModule<PBGaussSettings1>>(
                   addBackend<PBPPModule<PBPPSettings1>>(
                      addBackend<SATModule<SATSettings1>>(
                         addBackend<LRAModule<LRASettings1>>()
                        )
                    )
                ),
            });
        }
    };
}    // namespace smtrat
