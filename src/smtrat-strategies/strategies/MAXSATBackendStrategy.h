#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/PBPPModule/PBPPModule.h>

namespace smtrat {

    /**
     * This strategy is used as a artificial backend in the MaxSMT Module
     *
     * See MaxSMTSettings.h to adjust the used backend.
     */
    class MaxSATBackendStrategy:
        public Manager
    {
        public:
            MaxSATBackendStrategy(): Manager()
            {
                setStrategy(
                {
                    addBackend<PBPPModule<PBPPSettings1>>(
                        addBackend<SATModule<SATSettings1>>()
                    ),
                });
            }
    };

} // namespace smtrat
