/**
 * @file UFStrategy.h
 */
#pragma once

#include <lib/solver/Manager.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/CurryModule/CurryModule.h>
#include <smtrat-modules/UnionFindModule/UnionFindModule.h>

namespace smtrat
{
    /**
     * Strategy description.
     *
     * @author      Henrich Lauko, Dominika Krejci
     * @since       2018
     * @version     0.1
     *
     */
    class UFStrategy:
        public Manager
    {
        public:

        UFStrategy(): Manager()
        {
            setStrategy(
            {
                addBackend<CurryModule<CurrySettings1>>(
                    addBackend<SATModule<SATSettings1>>(
                        addBackend<UnionFindModule<UnionFindSettings1>>()
                    )
                )
            });
        }
    };
} // namespace smtrat
