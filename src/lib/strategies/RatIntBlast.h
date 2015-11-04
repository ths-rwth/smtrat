/**
 * @file RatIntBlast.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/PreprocessingModule/PreprocessingModule.h"
#include "../modules/IncWidthModule/IncWidthModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/IntBlastModule/IntBlastModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/ICPModule/ICPModule.h"
#include "../modules/VSModule/VSModule.h"
#include "../modules/CADModule/CADModule.h"
#include "../modules/SATModule/SATModule.h"

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
    class RatIntBlast:
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

        RatIntBlast(): Manager()
        {
            setStrategy(
            {
//                addBackend<PreprocessingModule<PreprocessingSettings1>>(
//                {
                    addBackend<IncWidthModule<IncWidthSettings1>>(
                    {
//                        addBackend<SATModule<SATSettings1>>(
//                        {
                            addBackend<IntBlastModule<IntBlastSettings1>>(
                            {
//                                addBackend<SATModule<SATSettings1>>(
//                                {
//                                    addBackend<ICPModule<ICPSettings1>>(
//                                    {
//                                        addBackend<VSModule<VSSettings1>>(
//                                        {
//                                            addBackend<CADModule<CADSettings1>>()
//                                        })
//                                    })
//                                }).condition( &conditionEvaluation5 ),
                                addBackend<SATModule<SATSettings1>>().condition( &conditionEvaluation4 )
                            })
//                        })
                    })
//                })
            });
        }
    };
} // namespace smtrat