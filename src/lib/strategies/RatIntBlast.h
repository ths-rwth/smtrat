/**
 * @file RatIntBlast.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/PreprocessingModule/PreprocessingModule.h"
#include "../modules/IncWidthModule/IncWidthModule.h"
#include "../modules/IntBlastModule/IntBlastModule.h"
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

        public:

        RatIntBlast(): Manager()
        {
            setStrategy(
            {
//                addBackend<PreprocessingModule<PreprocessingSettings1>>(
//                {
                    addBackend<IncWidthModule<IncWidthSettings2>>(
                    {
//                        addBackend<SATModule<SATSettings1>>(
//                        {
                            addBackend<IntBlastModule<IntBlastSettings2>>(
                            {
                                addBackend<SATModule<SATSettings1>>()
                            })
//                        })
                    })
//                })
            });
        }
    };
} // namespace smtrat