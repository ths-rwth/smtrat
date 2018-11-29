/**
 * @file RatNIAnoBB.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/IncWidthModule/IncWidthModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/IntBlastModule/IntBlastModule.h"
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
    class RatNIAnoBB:
        public Manager
    {
        static bool conditionEvaluation5( carl::Condition _condition )
        {
            return ( (carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= _condition) );
        }

        static bool conditionEvaluation4( carl::Condition _condition )
        {
            return (  !(carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= _condition) );
        }

        public:

        RatNIAnoBB(): Manager()
        {
            setStrategy(
            {
                addBackend<FPPModule<FPPSettings1>>(
                {
                    addBackend<IncWidthModule<IncWidthSettings1>>(
                    {
//                            addBackend<SATModule<SATSettings1>>(
//                            {
                            addBackend<IntBlastModule<IntBlastSettings1>>(
                            {
                                addBackend<SATModule<SATSettings1>>(
                                {
                                    addBackend<ICPModule<ICPSettings2>>(
                                    {
                                        addBackend<VSModule<VSSettings2346>>(
                                        {
                                            addBackend<CADModule<CADSettingsReal>>()
                                        })
                                    })
                                }).condition( &conditionEvaluation5 ),
                                addBackend<SATModule<SATSettings1>>().condition( &conditionEvaluation4 )
                            })
//                            })
                    })
                })
            });
        }
    };
} // namespace smtrat