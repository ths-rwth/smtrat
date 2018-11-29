/**
 * @file RatVSPlain.h
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
    class RatVSPlain:
        public Manager
    {
        public:

        RatVSPlain(): Manager()
        {
            setStrategy(
            {
                addBackend<SATModule<SATSettings1>>(
                    addBackend<VSModule<VSSettingsPlain>>()
                )
            });
        }
    };
} // namespace smtrat
