/**
 * @file NIASolver.h
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
    class NIASolver:
        public Manager
    {
        public:
            NIASolver(): Manager()
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
                        })
                    })
                });
            }
    };
} // namespace smtrat