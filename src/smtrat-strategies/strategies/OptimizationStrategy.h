#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/LRAModule/LRAModule.h>
#include <smtrat-modules/PBPPModule/PBPPModule.h>
#include <smtrat-modules/FPPModule/FPPModule.h>

namespace smtrat {

    /**
     * A backend compatible with optimization.
     */
    class OptimizationStrategy:
        public Manager
    {
        public:
            OptimizationStrategy(): Manager()
            {
                setStrategy(
                {
                    //addBackend<FPPModule<FPPSettingsOptimization>>(
                        //addBackend<PBPPModule<PBPPSettings1>>(
                            addBackend<SATModule<SATSettings1>>(
                                addBackend<LRAModule<LRASettings1>>()
                            )
                        //),
                    //)
                });
            }
    };

} // namespace smtrat
