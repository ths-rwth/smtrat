/**
 * @file LRASolver.h
 */
#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/FourierMotzkinModule/FourierMotzkinModule.h>

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
    class FouMoSolver:
        public Manager
    {
        public:
            FouMoSolver(): Manager()
            {
                setStrategy(
                {
                        addBackend<SATModule<SATSettings1>>(
                        {
                            addBackend<FourierMotzkinModule<FourierMotzkinSettings1>>()
                        })
                });
            }
    };
} // namespace smtrat
