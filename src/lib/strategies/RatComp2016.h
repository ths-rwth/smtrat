/**
 * @file RatComp2016.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/IncWidthModule/IncWidthModule.h"
#include "../modules/IntBlastModule/IntBlastModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/LRAModule/LRAModule.h"
#include "../modules/VSModule/VSModule.h"
#include "../modules/CADModule/CADModule.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/LRAModule/LRAModule.h"
#include "../modules/VSModule/VSModule.h"
#include "../modules/CADModule/CADModule.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/CubeLIAModule/CubeLIAModule.h"
#include "../modules/LRAModule/LRAModule.h"
#include "../modules/VSModule/VSModule.h"
#include "../modules/CADModule/CADModule.h"
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
    class RatComp2016:
        public Manager
    {
        static bool conditionEvaluation10( carl::Condition _condition )
        {
            return ( (carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= _condition) );
        }

        static bool conditionEvaluation11( carl::Condition _condition )
        {
            return ( (carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= _condition) );
        }

        static bool conditionEvaluation17( carl::Condition _condition )
        {
            return (  !(carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= _condition) );
        }

        static bool conditionEvaluation0( carl::Condition _condition )
        {
            return (  !(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= _condition) );
        }

        static bool conditionEvaluation1( carl::Condition _condition )
        {
            return ( (carl::PROP_IS_LITERAL_CONJUNCTION <= _condition) );
        }

        static bool conditionEvaluation2( carl::Condition _condition )
        {
            return (  !(carl::PROP_IS_LITERAL_CONJUNCTION <= _condition) );
        }

        public:

        RatComp2016(): Manager()
        {
            setStrategy(
            {
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
                    }).condition( &conditionEvaluation11 ),
                    addBackend<FPPModule<FPPSettings1>>(
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
                    }).condition( &conditionEvaluation17 )
                }).condition( &conditionEvaluation10 ),
                addBackend<FPPModule<FPPSettings1>>(
                {
                    addBackend<SATModule<SATSettings1>>(
                    {
                        addBackend<CubeLIAModule<CubeLIASettings1>>(
                        {
                            addBackend<LRAModule<LRASettings1>>(
                            {
                                addBackend<VSModule<VSSettings234>>(
                                {
                                    addBackend<CADModule<CADSettingsSplitFirst>>()
                                })
                            })
                        })
                    }).condition( &conditionEvaluation1 ),
                    addBackend<SATModule<SATSettings1>>(
                    {
                        addBackend<LRAModule<LRASettings1>>(
                        {
                            addBackend<VSModule<VSSettings234>>(
                            {
                                addBackend<CADModule<CADSettingsSplitFirst>>()
                            })
                        })
                    }).condition( &conditionEvaluation2 )
                }).condition( &conditionEvaluation0 )
            });
        }
    };
} // namespace smtrat