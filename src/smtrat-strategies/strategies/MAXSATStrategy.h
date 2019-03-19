/**
 * @file LRASolver.h
 */
#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/PBPPModule/PBPPModule.h>
#include <smtrat-modules/MaxSMTModule/MaxSMTModule.h>

namespace smtrat
{

    class MAXSATStrategy: public Manager
    {
        public:
            MAXSATStrategy(): Manager()
            {
                setStrategy({
                    addBackend<MaxSMTModule<MaxSMTSettingsFuMalikIncrementalSAT>>(
                        // The backend is defined in the settings!
                        // addBackend<PBPPModule<PBPPSettings1>>(
                        //     addBackend<SATModule<SATSettings1>>()
                        // )
                    ),
                });
            }
    };
}
