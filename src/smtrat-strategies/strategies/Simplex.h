/**
 * @file LRASolver.h
 */
#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/SimplexModule/SimplexModule.h>

namespace smtrat {
/**
 * Strategy description.
 *
 * @author
 * @since
 * @version
 *
 */
class Simplex : public Manager
{
    public:
        Simplex(): Manager()
        {
            setStrategy(
            {
                addBackend<FPPModule<FPPSettings1>>(
                {
                    addBackend<SATModule<SATSettings1>>(
                    {
                        addBackend<SimplexModule<SimplexSettings1>>()
                    })
                })
            });
        }
};

} // namespace smtrat
