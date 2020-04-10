/**
 * @file NRASolver.h
 */
#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/STropModule/STropModule.h>
#include <smtrat-modules/ICPModule/ICPModule.h>
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
    class NRASolver:
        public Manager
    {
        public:
            NRASolver(): Manager()
            {
                setStrategy(
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
                });
            }
    };
} // namespace smtrat
