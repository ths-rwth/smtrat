/**
 * @file RatTwo.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/PreprocessingModule/PreprocessingModule.h"
#include "../modules/SATModule/SATModule.h"
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
    class RatTwo:
        public Manager
    {
        public:

        RatTwo(): Manager()
        {
            size_t PreprocessingModule33 = 0, ICPModule32 = 0, SATModule31 = 0, Start28 = 0, CADModule29 = 0, VSModule30 = 0;
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
                                addBackend<CADModule<CADSettings1>>().id( CADModule29 )
                            }).id( VSModule30 )
                        }).id( ICPModule32 )
                    }).id( SATModule31 )
                }).id( PreprocessingModule33 )
            });
        }
    };
} // namespace smtrat