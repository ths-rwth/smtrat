/**
 * @file RatOneNoBB.h
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
    class RatOneNoBB:
        public Manager
    {
        public:

        RatOneNoBB(): Manager()
        {
            setStrategy(
            {
                addBackend<FPPModule<FPPSettings1>>(
                {
                    addBackend<SATModule<SATSettings1>>(
                    {
//                        addBackend<CubeLIAModule<CubeLIASettings1>>(
//                        {   
                            addBackend<LRAModule<LRASettings1>>(
                            {
                                addBackend<VSModule<VSSettings2346>>(
                                {
                                    addBackend<CADModule<CADSettingsReal>>()
                                })
                            })
//                        })
                    })
                })
            });
        }
    };
} // namespace smtrat