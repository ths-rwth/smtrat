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
    /**
     * Strategy description.
     *
     * @author
     * @since
     * @version
     *
     */
    class MAXSATStrategy:
        public Manager
    {
        public:
            MAXSATStrategy(): Manager()
            {
                setStrategy(
                {
                        addBackend<MaxSMTModule<MaxSMTSettingsLinearSearch>>(
                        {
                            addBackend<PBPPModule<PBPPSettings1>>(
                                addBackend<SATModule<SATSettings1>>()
                            )
                        })
                });
            }
    };
} // namespace smtrat
