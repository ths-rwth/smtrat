/**
 * @file RatNIA.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/CubeLIAModule/CubeLIAModule.h"
#include "../modules/LRAModule/LRAModule.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/IncWidthModule/IncWidthModule.h"
#include "../modules/IntBlastModule/IntBlastModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/LRAModule/LRAModule.h"
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
    class RatNIA:
        public Manager
    {
        static bool conditionEvaluation7( carl::Condition _condition )
        {
            return (  !(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= _condition) );
        }

        static bool conditionEvaluation0( carl::Condition _condition )
        {
            return ( (carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= _condition) );
        }

        public:

        RatNIA(): Manager()
        {
            setStrategy(
            {
                addBackend<SATModule<SATSettings1>>(
                {
                    addBackend<CubeLIAModule<CubeLIASettings1>>(
                    {
                        addBackend<LRAModule<LRASettings1>>()
                    })
                }).condition( &conditionEvaluation7 ),
                addBackend<FPPModule<FPPSettings1>>(
                {
                    addBackend<IncWidthModule<IncWidthSettings1>>(
                    {
                        addBackend<IntBlastModule<IntBlastSettings2>>(
                        {
                            addBackend<SATModule<SATSettings1>>(
                            {
                                addBackend<LRAModule<LRASettings1>>(
                                {
                                    addBackend<VSModule<VSSettings234>>(
                                    {
                                        addBackend<CADModule<CADSettingsSplitFirst>>()
                                    })
                                })
                            })
                        })
                    })
                }).condition( &conditionEvaluation0 )
            });
        }
    };
} // namespace smtrat