#pragma once

#include <smtrat-solver/Manager.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/LRAModule/LRAModule.h>
#include <smtrat-modules/NRAILModule/NRAILModule.h>

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
    class NRARefinement_Solver3:
            public Manager
    {
    public:
        NRARefinement_Solver3(): Manager()
        {
            setStrategy(
            {
                addBackend<NRAILModule<NRAILSettings3>>(
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
