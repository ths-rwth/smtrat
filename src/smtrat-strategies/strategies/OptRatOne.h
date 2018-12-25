/**
 * @file OptRatOne.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/LRAModule/LRAModule.h"
#include "../modules/CubeLIAModule/CubeLIAModule.h"
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
    class OptRatOne:
        public Manager
    {
        public:

        OptRatOne(): Manager()
        {
            setStrategy(
            {
//                addBackend<FPPModule<FPPSettings1>>(
//                {
                    addBackend<SATModule<SATSettings1>>(
                    {
//                        addBackend<CubeLIAModule<CubeLIASettings1>>(
//                        {   
                            addBackend<LRAModule<LRASettings2>>(
                            {
//                                addBackend<VSModule<VSSettings234>>(
//                                {
//                                    addBackend<CADModule<CADSettingsSplitPath>>()
//                                })
                            })
//                        })
                    })
//                })
            });
        }
    };
} // namespace smtrat