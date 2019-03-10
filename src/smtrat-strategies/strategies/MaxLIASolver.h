/**
 * @file LRASolver.h
 */
#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/LRAModule/LRAModule.h>
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
    class MaxLIASolver:
        public Manager
    {
        public:
            MaxLIASolver(): Manager()
            {
                setStrategy(
                {
                        addBackend<MaxSMTModule<MaxSMTSettings1>>(
                        {
                            addBackend<SATModule<SATSettings1>>(
                            {
                                addBackend<LRAModule<LRASettings1>>()
                            })
                        })
                });
            }
    };
} // namespace smtrat
