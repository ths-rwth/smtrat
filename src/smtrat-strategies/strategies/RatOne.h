/**
 * @file RatOne.h
 */
#pragma once

#include <smtrat-solver/Manager.h>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/LRAModule/LRAModule.h>
#include <smtrat-modules/CubeLIAModule/CubeLIAModule.h>
#include <smtrat-modules/VSModule/VSModule.h>
#include <smtrat-modules/CADModule/CADModule.h>

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
    class RatOne:
        public Manager
    {
        public:

        RatOne(): Manager()
        {
            setStrategy(
            {
                addBackend<FPPModule<FPPSettings1>>(
                    addBackend<SATModule<SATSettings1>>(
//                        addBackend<CubeLIAModule<CubeLIASettings1>>(
                            addBackend<LRAModule<LRASettings1>>(
                                addBackend<VSModule<VSSettings234>>(
                                    addBackend<CADModule<CADSettingsSplitFirst>>()
                                )
                            )
//                        )
                    )
                )
            });
        }
    };
} // namespace smtrat
