/**
 * @file RatICPVS.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/ICPModule/ICPModule.h"
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
    class RatICPVS:
        public Manager
    {
        public:

        RatICPVS(): Manager()
        {
            setStrategy(
            {
                addBackend<SATModule<SATSettings1>>(
                {
                    addBackend<ICPModule<ICPSettings1>>(
                    {
                        addBackend<VSModule<VSSettingsOnlyVB>>()
                    })
                })
            });
        }
    };
} // namespace smtrat