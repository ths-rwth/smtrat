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
    class NRARefinementSolver24:
            public Manager
    {
    public:
        NRARefinementSolver24(): Manager()
        {
            setStrategy(
                    {
                            addBackend<NRAILModule<NRAILSettings24>>(
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
