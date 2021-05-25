/**
 * @file RatComp2016.h
 */
#pragma once

#include <smtrat-solver/Manager.h>
#include <smtrat-modules/CubeLIAModule/CubeLIAModule.h>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/IncWidthModule/IncWidthModule.h>
#include <smtrat-modules/IntBlastModule/IntBlastModule.h>
#include <smtrat-modules/ICPModule/ICPModule.h>
#include <smtrat-modules/LRAModule/LRAModule.h>
#include <smtrat-modules/NewCADModule/NewCADModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/VSModule/VSModule.h>

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
    class SMTCOMP:
        public Manager
    {
        static bool conditionEvaluation6( carl::Condition _condition )
        {
            return ( (carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= _condition) && (carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= _condition) );
        }

        static bool conditionEvaluation16( carl::Condition _condition )
        {
            return ( (carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= _condition) &&  !(carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= _condition) );
        }

        static bool conditionEvaluation0( carl::Condition _condition )
        {
            return (  !(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= _condition) && (carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= _condition) );
        }

        static bool conditionEvaluation1( carl::Condition _condition )
        {
            return ( (carl::PROP_IS_LITERAL_CONJUNCTION <= _condition) );
        }

        static bool conditionEvaluation2( carl::Condition _condition )
        {
            return (  !(carl::PROP_IS_LITERAL_CONJUNCTION <= _condition) );
        }

        static bool conditionEvaluation13( carl::Condition _condition )
        {
            return (  !(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= _condition) &&  !(carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= _condition) );
        }

        public:

        SMTCOMP(): Manager()
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
                                        addBackend<NewCADModule<NewCADSettingsFOS>>()
                                    })
                                })
                            })
                        })
                    })
                }).condition( &conditionEvaluation6 ),
                addBackend<FPPModule<FPPSettings1>>(
                {
                    addBackend<SATModule<SATSettings1>>(
                    {
                        addBackend<STropModule<STropSettings1>>(
                        {
                            addBackend<ICPModule<ICPSettings1>>(
                            {
                                addBackend<VSModule<VSSettings234>>(
                                {
                                    addBackend<NewCADModule<NewCADSettingsFOS>>()
                                })
                            })
                        })
                    })
                })).condition( &conditionEvaluation16 ),
                addBackend<FPPModule<FPPSettings1>>(
                {
                    addBackend<SATModule<SATSettings1>>(
                    {
                        addBackend<CubeLIAModule<CubeLIASettings1>>(
                        {
                            addBackend<LRAModule<LRASettings1>>()
                        })
                    }).condition( &conditionEvaluation1 ),
                    addBackend<SATModule<SATSettings1>>(
                    {
                        addBackend<LRAModule<LRASettings1>>()
                    }).condition( &conditionEvaluation2 )
                }).condition( &conditionEvaluation0 ),
                addBackend<FPPModule<FPPSettings1>>(
                {
                    addBackend<SATModule<SATSettings1>>(
                    {
                        addBackend<LRAModule<LRASettings1>>()
                    })
                }).condition( &conditionEvaluation13 )
            });
        }
    };
} // namespace smtrat
