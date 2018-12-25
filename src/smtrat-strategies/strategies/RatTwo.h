/**
 * @file RatTwo.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/ICPModule/ICPModule.h"
#include "../modules/VSModule/VSModule.h"
#include "../modules/CADModule/CADModule.h"

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
    class RatTwo:
        public Manager
    {
        public:

        RatTwo(): Manager()
        {
            setStrategy(
            {
                addBackend<FPPModule<FPPSettings1>>(
                {
                    addBackend<SATModule<SATSettings1>>(
                    {
                        addBackend<ICPModule<ICPSettings1>>(
                        {
                            addBackend<VSModule<VSSettings234>>(
                            {
                                addBackend<CADModule<CADSettingsSplitFirst>>()
                            })
                        })
                    })
                })
            });
        }
    };
} // namespace smtrat
