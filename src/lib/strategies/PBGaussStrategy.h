#pragma once

#include "../solver/Manager.h"

#include "../modules/LRAModule/PBGaussModule.h"
#include "../modules/PBPPModule/PBPPModule.h"



namespace smtrat
{
    class PBPPStrategy:
    public Manager
    {
    public:
        PBPPStrategy(): Manager() {
            setStrategy({
                addBackend<PBGaussModule<PBGaussSettings1>>(
                    addBackend<PBPPModule<PBPPSettings1>>()
                ),
            });
        }
    };
}    // namespace smtrat
