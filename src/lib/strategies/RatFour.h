/**
 * @file RatFour.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/PreprocessingModule/PreprocessingModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/ICPModule/ICPModule.h"
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
    class RatFour:
        public Manager
    {
        public:

        RatFour(): Manager()
        {
            size_t Start1 = 0, CADModule4 = 0, SATModule10 = 0, PreprocessingModule3 = 0, LRAModule5 = 0, CADModule2 = 0, ICPModule7 = 0, SATModule6 = 0, VSModule9 = 0, VSModule8 = 0;
            setStrategy(
            {
                addBackend<PreprocessingModule<PreprocessingSettings1>>(
                {
                    addBackend<SATModule<SATSettings1>>(
                    {
                        addBackend<ICPModule<ICPSettings1>>(
                        {
                            addBackend<VSModule<VSSettings1>>(
                            {
                                addBackend<CADModule<CADSettings1>>().id( CADModule4 )
                            }).id( VSModule8 )
                        }).id( ICPModule7 )
                    }).id( SATModule10 ),
                    addBackend<SATModule<SATSettings1>>(
                    {
                        addBackend<LRAModule<LRASettings1>>(
                        {
                            addBackend<VSModule<VSSettings1>>(
                            {
                                addBackend<CADModule<CADSettings1>>().id( CADModule2 )
                            }).id( VSModule9 )
                        }).id( LRAModule5 )
                    }).id( SATModule6 )
                }).id( PreprocessingModule3 )
            });
        }
    };
} // namespace smtrat