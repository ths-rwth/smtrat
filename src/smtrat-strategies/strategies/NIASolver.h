/**
 * @file NIASolver.h
 */
#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/IncWidthModule/IncWidthModule.h>
#include <smtrat-modules/IntBlastModule/IntBlastModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/LRAModule/LRAModule.h>
#include <smtrat-modules/VSModule/VSModule.h>
#include <smtrat-modules/NewCADModule/NewCADModule.h>

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
                        addBackend<IncWidthModule<IncWidthSettings1>>(
                            addBackend<IntBlastModule<IntBlastSettings2>>(
                                addBackend<SATModule<SATSettings1>>(
                                    addBackend<LRAModule<LRASettings1>>(
                                        addBackend<VSModule<VSSettings234>>(
                                            addBackend<NewCADModule<NewCADSettingsFOS>>()
                                        )
                                    )
                                )
                            )
                        )
                    )
                });
            }
    };
} // namespace smtrat
