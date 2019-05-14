/**
 * @file UFStrategy.h
 */
#pragma once

#include <smtrat-solver/Manager.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/UnionFindModule/UnionFindModule.h>
#include <smtrat-modules/UFCegarModule/UFCegarModule.h>
//#include <smtrat-modules/CurryModule/CurryModule.h>

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
                addBackend<UFCegarModule<UFCegarSettings1>>(
                    addBackend<SATModule<SATSettings1>>(
                        addBackend<UnionFindModule<UnionFindSettings1>>()
                    )
                )
            });
        }
    };
} // namespace smtrat
