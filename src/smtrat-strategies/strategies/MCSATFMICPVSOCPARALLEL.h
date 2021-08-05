#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
    class MCSATFMICPVSOCPARALLEL: public Manager
    {
    public:
        MCSATFMICPVSOCPARALLEL(): Manager() {
            setStrategy(
                    addBackend<SATModule<SATSettingsMCSATFMICPVSOCPARALLEL>>()
            );
        }
    };
}	// namespace smtrat