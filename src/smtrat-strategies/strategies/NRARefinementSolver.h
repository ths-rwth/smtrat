#pragma once

#include "lib/solver/Manager.h"
#include "smtrat-modules/SATModule/SATModule.h"
#include "smtrat-modules/LRAModule/LRAModule.h"
#include "smtrat-modules/AbstractModule/AbstractModule.h"

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
                        addBackend<LRAModule<LRASettings1>>()
                    })
                })
            });
        }
    };
} // namespace smtrat
