/**
 * @file LIASolver.h
 */
#pragma once

#include "../solver/Manager.h"

#include "../modules/FPPModule/FPPModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/CubeLIAModule/CubeLIAModule.h"
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
    class LIASolver:
        public Manager
    {
        public:
            LIASolver(): Manager()
            {
                //TODO je einmal auf allen Benchmarks laufen lassen und dann Kombination mit Conditions
                static bool conditionEvaluation1( carl::Condition _condition )
                {
                    return ( (carl::PROP_IS_LITERAL_CONJUNCTION <= _condition) );
                }

                static bool conditionEvaluation2( carl::Condition _condition )
                {
                    return (  !(carl::PROP_IS_LITERAL_CONJUNCTION <= _condition) );
                }

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
                        }).condition( &conditionEvaluation1 ),
                        addBackend<SATModule<SATSettings1>>(
                        {
                            addBackend<LRAModule<LRASettings1>>()
                        }).condition( &conditionEvaluation2 )
                    })
                });
            }
    };
} // namespace smtrat