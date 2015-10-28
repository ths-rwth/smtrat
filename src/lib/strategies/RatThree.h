/**
 * @file RatThree.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/PreprocessingModule/PreprocessingModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/LRAModule/LRAModule.h"
#include "../modules/VSModule/VSModule.h"
#include "../modules/CADModule/CADModule.h"
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
    class RatThree:
        public Manager
    {
        public:

        RatThree(): Manager()
        {
            size_t CADModule5 = 0, VSModule3 = 0, SATModule2 = 0, Start1 = 0, LRAModule6 = 0, PreprocessingModule4 = 0, CADModule11 = 0;
            setStrategy(
            {
                addBackend<PreprocessingModule<PreprocessingSettings1>>(
                {
                    addBackend<SATModule<SATSettings1>>(
                    {
                        addBackend<LRAModule<LRASettings1>>(
                        {
                            addBackend<VSModule<VSSettings1>>(
                            {
                                addBackend<CADModule<CADSettings1>>().id( CADModule5 )
                            }).id( VSModule3 ),
                            addBackend<CADModule<CADSettings1>>().id( CADModule11 )
                        }).id( LRAModule6 )
                    }).id( SATModule2 )
                }).id( PreprocessingModule4 )
            });
        }
    };
} // namespace smtrat