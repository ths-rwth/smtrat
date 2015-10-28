/**
 * @file RatOne.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/PreprocessingModule/PreprocessingModule.h"
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
    class RatOne:
        public Manager
    {
        public:

        RatOne(): Manager()
        {
            size_t Start22 = 0, VSModule24 = 0, SATModule25 = 0, CADModule23 = 0, LRAModule26 = 0, PreprocessingModule27 = 0;
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
                                addBackend<CADModule<CADSettings1>>().id( CADModule23 )
                            }).id( VSModule24 )
                        }).id( LRAModule26 )
                    }).id( SATModule25 )
                }).id( PreprocessingModule27 )
            });
        }
    };
} // namespace smtrat