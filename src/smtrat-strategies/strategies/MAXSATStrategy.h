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
                    /// NB! currently, LinearSearch is better than core guided algorithms since the smtrat-unsat-cores need more
                    /// iterations than the LinearSearch approach. If SATModule ever supports unsat cores directly, it might make sense
                    /// to use MSU3 or FuMalikIncremental. Both strategies are tested on small examples and do work.
                    /// Until then use LinearSearch!!!
                    addBackend<MaxSMTModule<MaxSMTSettingsLinearSearchSAT>>(
                        // The backend is defined in the settings!
                        // addBackend<PBPPModule<PBPPSettings1>>(
                        //     addBackend<SATModule<SATSettings1>>()
                        // )
                    ),
                });
            }
    };
}
