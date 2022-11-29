#pragma once

#include <smtrat-solver/Manager.h>

//#include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
    class MCSAT_FMICPVSOCPARALLEL: public Manager
    {
    public:
        MCSAT_FMICPVSOCPARALLEL(): Manager() {
            setStrategy(
                    addBackend<SATModule<SATSettingsMCSATFMICPVSOCPARALLEL>>()
            );
        }
    };
}	// namespace smtrat