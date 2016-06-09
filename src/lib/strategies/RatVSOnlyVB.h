/**
 * @file RatVSOnlyVB.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/VSModule/VSModule.h"

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
    class RatVSOnlyVB:
        public Manager
    {
        public:

        RatVSOnlyVB(): Manager()
        {
            setStrategy(
            {
                addBackend<SATModule<SATSettings1>>(
                    addBackend<VSModule<VSSettingsOnlyVB>>()
                )
            });
        }
    };
} // namespace smtrat
