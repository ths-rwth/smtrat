/**
 * @file RatComp2016PL.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/CubeLIAModule/CubeLIAModule.h"
#include "../modules/LRAModule/LRAModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/LRAModule/LRAModule.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/IncWidthModule/IncWidthModule.h"
#include "../modules/IntBlastModule/IntBlastModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/LRAModule/LRAModule.h"
#include "../modules/VSModule/VSModule.h"
#include "../modules/CADModule/CADModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/LRAModule/LRAModule.h"
#include "../modules/ICPModule/ICPModule.h"
#include "../modules/VSModule/VSModule.h"
#include "../modules/CADModule/CADModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/LRAModule/LRAModule.h"
#include "../modules/CADModule/CADModule.h"
#include "../modules/VSModule/VSModule.h"
#include "../modules/CADModule/CADModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/ICPModule/ICPModule.h"
#include "../modules/VSModule/VSModule.h"
#include "../modules/CADModule/CADModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/LRAModule/LRAModule.h"

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
    class RatComp2016PL:
        public Manager
    {
        static bool conditionEvaluation0( carl::Condition _condition )
        {
            return (  !(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= _condition) );
        }

        static bool conditionEvaluation6( carl::Condition _condition )
        {
            return ( (carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= _condition) );
        }

        static bool conditionEvaluation7( carl::Condition _condition )
        {
            return ( (carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= _condition) );
        }

        static bool conditionEvaluation23( carl::Condition _condition )
        {
            return (  !(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= _condition) );
        }

        public:

        RatComp2016PL(): Manager()
        {
            setStrategy(
            {
                addBackend<FPPModule<FPPSettings1>>(
                {
                    addBackend<SATModule<SATSettings1>>(
                    {
                        addBackend<CubeLIAModule<CubeLIASettings1>>(
                        {
                            addBackend<LRAModule<LRASettings1>>()
                        })
                    }),
                    addBackend<SATModule<SATSettings1>>(
                    {
                        addBackend<LRAModule<LRASettings1>>()
                    })
                }).condition( &conditionEvaluation0 ),
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
                    }).condition( &conditionEvaluation7 ),
                    addBackend<SATModule<SATSettings1>>(
                    {
                        addBackend<LRAModule<LRASettings1>>(
                        {
                            addBackend<ICPModule<ICPSettings1>>(
                            {
                                addBackend<VSModule<VSSettings234>>(
                                {
                                    addBackend<CADModule<CADSettingsSplitFirst>>()
                                })
                            })
                        })
                    }),
                    addBackend<SATModule<SATSettings1>>(
                    {
                        addBackend<LRAModule<LRASettings1>>(
                        {
                            addBackend<CADModule<CADSettingsSplitFirst>>(),
                            addBackend<VSModule<VSSettings234>>(
                            {
                                addBackend<CADModule<CADSettingsSplitFirst>>()
                            })
                        })
                    }),
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
                }).condition( &conditionEvaluation6 ),
                addBackend<SATModule<SATSettings1>>(
                {
                    addBackend<LRAModule<LRASettings1>>()
                }).condition( &conditionEvaluation23 )
            });
        }
    };
} // namespace smtrat