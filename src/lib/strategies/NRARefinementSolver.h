#pragma once

#include "../solver/Manager.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/LRAModule/LRAModule.h"
#include "../modules/AbstractModule/AbstractModule.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/STropModule/STropModule.h"
#include "../modules/ICPModule/ICPModule.h"
#include "../modules/VSModule/VSModule.h"
#include "../modules/NewCADModule/NewCADModule.h"

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
    class NRARefinementSolver:
            public Manager
    {
    public:
        NRARefinementSolver(): Manager()
        {
            setStrategy(
            {
                addBackend<AbstractModule<AbstractSettings1>>(
                {
                    addBackend<SATModule<SATSettings1>>(
                    {
                        addBackend<LRAModule<LRASettings1>>(
                        {
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
                            })
                        })
                    })
                })
            });
        }
    };
} // namespace smtrat
