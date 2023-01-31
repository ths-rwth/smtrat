/**
 * @file LRASolver.h
 */
#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/NoIncSimplexModule/NoIncSimplexModule.h>

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
    class NoIncSimplexNoPP:
        public Manager
    {
        public:
            NoIncSimplexNoPP(): Manager()
            {
                setStrategy(
                {
                    addBackend<SATModule<SATSettings1>>(
                    {
                        addBackend<NoIncSimplexModule<NoIncSimplexSettings1>>()
                    })
                });
            }
    };
} // namespace smtrat
