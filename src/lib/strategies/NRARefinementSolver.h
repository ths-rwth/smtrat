#pragma once

#include "../solver/Manager.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/LRAModule/LRAModule.h"
#include "../modules/AbstractModule/AbstractModule.h"

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
